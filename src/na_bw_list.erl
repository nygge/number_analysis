%%%-------------------------------------------------------------------
%%% @copyright 1995 Claes Wikstrom (klacke@erix.eicsson.se)
%%% @author Claes Wikstrom <klacke@erix.eicsson.se>
%%% @author Sean Hinde <sean.hinde@gmail.com>
%%% @author Anders Nygren <anders.nygren@txm.com.mx>
%%% @doc Provides a Black/White list checker for dialled numbers
%%%
%%% bw_list provides functions to create lists of phone numbers which should be
%%% barred or allowed and to check whether a dialled number matches. Numbers are
%%% checked on a digit by digit basis until either a match is made, a match is
%%% definitely not made, or no more digits are left. Each new list which is created
%%% is implemented using a single Mnesia table which may be replicated on a number
%%% of Erlang Nodes. 
%%%
%%% Within each new table multiple lists of numbers may be built indexed by two
%%% further groupings called Ref and Name. Functions are provided to create new
%%% tables, add lists within a table, add entries to lists within the table,
%%% retrieve all lists contained in a table, retrieve all the phone numbers
%%% associated with a Ref/Name within a table, as well as looking up and
%%% deleting entries.
%%%
%%% This module was posted on the erlang-questions mailing list
%%% [http://www.erlang.org/ml-archive/erlang-questions/200401/msg00009.html]
%%% by Sean Hinde.
%%% == Database Design ==
%%% bw_list use 1 fixed mnesia table
%%% <ul>
%%% <li>bw_lists</li>
%%% </ul>
%%% And one table for each black/white list class defined.
%%% <ul>
%%% <li>"list_name"</li>
%%% </ul>
%%%
%%% === bw_lists ===
%%% Stores definition of bw_lists
%%% <table border="1">
%%%   <tr>
%%%     <th>Record Name</th>
%%%     <td>{@link bw_lists()}</td>
%%%   </tr>
%%%   <tr>
%%%     <th>Table Type</th>
%%%     <td>set</td>
%%%   </tr>
%%%   <tr>
%%%     <th>Indexes</th>
%%%     <td>none</td>
%%%   </tr>
%%% </table>
%%%
%%% === list ===
%%% Stores bw_lists
%%% <table border="1">
%%%   <tr>
%%%     <th>Record Name</th>
%%%     <td>{@link number_analyser()}</td>
%%%   </tr>
%%%   <tr>
%%%     <th>Table Type</th>
%%%     <td>set</td>
%%%   </tr>
%%%   <tr>
%%%     <th>Indexes</th>
%%%     <td>none</td>
%%%   </tr>
%%% </table>
%%% @end 
%%%-------------------------------------------------------------------

-module(na_bw_list).
-export([mnesia_table/0, mnesia_table/1, new/1, new/2]).
-export([add_list/4, all_lists/2, print_all/3, check/4, delete/5, insert/6,
	 delete_list/3, list_info/3]).
-export([debug_print/3]).

%% @type number_analyser() = #number_analyser{num=Key,res=Result}
%% Key = {Ref,Name,Prefix}
%% Ref = term()
%% Name = term()
%% Result = get_more_digits | {get_more_digits, Value} | Value
%% Value = term().
-record(number_analyser, {num = [],
			  res = null}).

%% @type bw_lists() = #bw_lists{list_id=Key,username=UserName,timestamp=Timestamp}
%% Key = {Table,Ref,Name}
%% Table = atom()
%% Ref = term()
%% Name = term()
%% Timestamp = datetime().
-record(bw_lists, {list_id,
                   username,
                   timestamp}).

%% API

%% Create a new analysis table. List would be e.g. black or white
%%--------------------------------------------------------------------
%% @spec new(Type) -> {atomic, ok} | {aborted, Reason}
%% @equiv new(Type,[node()])
%% @doc 
%% @end
%%--------------------------------------------------------------------
new(Type) ->
    new(Type, [node()]).

%%--------------------------------------------------------------------
%% @spec new(Type, Nodes) -> {atomic, ok} | {aborted, Reason}
%% @doc This function creates a new table called Type where type must be an
%% atom. e.g. Type could be black, to contain all black lists for an application.
%% If a list of node names are specified, the table is replicated on all those
%% nodes, otherwise the table is created on the local node only.
%% @end
%%--------------------------------------------------------------------
new(Type, Nodes) ->
    mnesia:create_table(Type,
                        [{attributes, record_info(fields, number_analyser)},
			 {record_name, number_analyser},
                         {disc_copies, Nodes}]).

%%--------------------------------------------------------------------
%% @spec add_list(Type, Ref, Name, UserName) -> ok | {error, Reason}
%% @doc This function adds a new list to the table Type which will be
%% referenced by Ref and Name. This must be done before any numbers can be
%% added to the table for this Ref/Name.
%% @end
%%--------------------------------------------------------------------
add_list(Type, Ref, Name, UserName) ->
    F = fun() ->
		case get_tables(number_analyser) of
		    [] ->
			mnesia:abort(no_types_defined);
		    Tables ->
			case lists:member(Type, Tables) of
			    false ->
				mnesia:abort(type_not_defined);
			    true ->
                                case mnesia:wread({bw_lists,{Type, Ref, Name}}) of
                                     [] ->
				          mnesia:write(#bw_lists{
						       list_id = {Type, Ref, Name},
                                                       username = UserName,
                                                       timestamp = {date(), time()} });
                                     _ ->
                                          mnesia:abort(list_already_defined)
                                 end
			end
		end
	end,
    case mnesia:transaction(F) of
	{atomic, _} ->
	    ok;
	{aborted, Reason} ->
	    {error, Reason}
    end.

%%--------------------------------------------------------------------
%% @spec all_lists(Type, Ref) -> [{Name, Ref}] | {error, Reason}
%% @doc This function retrieves an erlang list of {Name, Ref} for all Lists
%% in table Type with reference Ref.
%% @end
%%--------------------------------------------------------------------
all_lists(Type, Ref) ->
    WildPat = mnesia:table_info(bw_lists, wild_pattern),
    Pat = WildPat#bw_lists{list_id={Type,Ref, '_'}},
    F = fun() -> mnesia:match_object(Pat) end,
    case mnesia:transaction(F) of
	{atomic, List} ->
	    lists:map(fun(#bw_lists{list_id={_B,C,D}}) -> {D, C} end, List);
	{aborted, Reason} ->
	    {error, Reason}
    end.


%%--------------------------------------------------------------------
%% @spec check(Type, Ref, Name, Numberlist) -> Result | no_match
%% @doc This function looks up a telephone number in the form 
%% [0,1,8,1,2,1,4,2,4,1,3] digit by digit. If for example [0,1,8,1] is an
%% entry in the referenced List, this function will return the value stored
%% against [0,1,8,1]. If no match is found returns no_match.
%% @end
%%--------------------------------------------------------------------
check(Type, Ref, Name, Numberlist) ->
    case try_lookup(Type, Ref, Name, Numberlist) of
	{found, Result} ->
	    Result;
	What ->
	    What
%%	    no_match
    end.

%% Big problem. If we are deleting a number which is part of the subtree of another
%% Number we need to just turn it into 'get_more_digits'
%% If it isn't, we need to delete the number, and all parts of its subtree 
%% which are not parts of the subtree of another valid entry.
%%--------------------------------------------------------------------
%% @spec delete(T, Ref, Name, UserName, NumList) -> ok | {error, Reason}
%% @doc This function attempts to delete the entry referenced. If Numberlist is
%% a prefix of a number already in the table this command is rejected with
%% Reason trying_to_delete_sublist.
%% @end
%%--------------------------------------------------------------------
delete(_,_,_,_,[]) -> {error, invalid_delete};
delete(T, Ref, Name, UserName, NumList) ->
    F = fun() ->
                Num = to_hex_integer(process_numberlist(NumList)),
                case mnesia:read(T, {Ref, Name, Num}, read) of
                    [#number_analyser{res=get_more_digits}] ->
                        mnesia:abort(trying_to_delete_sublist);
                    [_Val] ->
                        case mnesia:wread({bw_lists, {T,Ref,Name}}) of
            		   [] ->
                               mnesia:abort(list_not_predefined);
                           [L] ->
                               mnesia:write(L#bw_lists{username = UserName,
                                          timestamp = {date(), time()} }),
                               try_delete(T, Ref, Name, NumList, Num)
                        end;
                    [] ->
                        mnesia:abort(number_not_found)
                end
        end,
    case mnesia:transaction(F) of
        {aborted, Reason} ->
            {error, Reason};
        {atomic, _} ->
            ok
    end.

try_delete(T, Ref, Name, Numlist, Num) ->
    %First get a list of all entries for this list
    Entries = ets:match(T, {number_analyser,{Ref,Name,'$1'},'$2'}),
    List_entries = lists:map(fun([X,Y]) -> {hex_to_phonenumber(X,[]),Y} end, Entries),
    case subtree(Numlist, List_entries, false) of
        yes ->
            mnesia:write(T, #number_analyser{num = {Ref, Name, Num},
                                             res = get_more_digits}, write);
        no ->
            mnesia:delete({T, {Ref,Name,Num}}),
            deltree(T, Ref, Name, lists:reverse(Numlist), lists:keydelete(Numlist, 1, List_entries))
    end.

deltree(T, Ref, Name, [_|Rev_num], List_entries) ->
    Num_ordered = lists:reverse(Rev_num),
    case subtree(Num_ordered, List_entries, true) of
        yes ->
            ok;
        no ->
            mnesia:delete({T, {Ref,Name,to_hex_integer(process_numberlist(Num_ordered))}}),
            deltree(T, Ref, Name, Rev_num, List_entries)
    end;
deltree(_T, _Ref, _Name, [], _) ->
    ok.

subtree(Numlist, [{_H,get_more_digits}|T], Findme) -> subtree(Numlist, T, Findme)
;
subtree(Numlist, [{Numlist,_}|T], false) -> subtree(Numlist, T, false); % don't find ourselves
subtree(Numlist, [{H, _Result}|T], Findme) ->
    case lists:prefix(Numlist, H) of
        true ->
            yes;
        false ->
            subtree(Numlist, T, Findme)
    end;
subtree(_Numlist, [], _Findme) -> no.

%%--------------------------------------------------------------------
%% @spec delete_list(T, Ref, Name) ->  ok | {error, Reason}
%% @doc This function attempts to delete all entries in table Type referenced
%% by Ref.
%% @end
%%--------------------------------------------------------------------
delete_list(T, Ref, Name) ->
   F = fun() ->
         case mnesia:wread({bw_lists,{T, Ref, Name}}) of
		    [] ->
			mnesia:abort(list_not_defined);
		    _ ->
			delete2(T, Ref, Name),
			mnesia:delete(bw_lists, {T, Ref, Name}, write)
		end
	end,
    case mnesia:transaction(F) of
	{aborted, Reason} ->
	    {error, Reason};
	{atomic, _} ->
	    ok
    end.

delete2(T, Ref, Name) ->
    WildPat = mnesia:table_info(T, wild_pattern),
    Pat = WildPat#number_analyser{num = {Ref, Name, '_'}},
    Entries = mnesia:match_object(T, Pat, read),
    lists:foreach(fun(X) ->
			  mnesia:delete_object(T, X, write)
		  end, Entries).

%%--------------------------------------------------------------------
%% @spec insert(T, Ref, Name, UserName, NumberList, Value) -> ok | {error, Reason}
%% @doc This function attempts to insert the number Numberlist (given as list
%% e.g [0,1,8,1]) into table Type, List Ref, Name. The List Ref/Name must have
%% been created using add_list/3 beforehand. Future matches against this number
%% by the check function will return the result Value.
%% @end
%%--------------------------------------------------------------------
insert(T, Ref, Name, UserName, NumberList, Value) ->
    F = fun() ->
	case mnesia:wread({bw_lists, {T,Ref,Name}}) of
	    [] ->
		mnesia:abort(list_not_predefined);
	    [L] ->
                mnesia:write(L#bw_lists{username = UserName,
                                       timestamp = calendar:universal_time()}),

		insert2(T, [], process_numberlist(NumberList), Value, Ref, Name)
	end
    end,
    case mnesia:transaction(F) of
	{aborted, Reason} ->
	    {error, Reason};
	{atomic, _} ->
	    ok
    end.

%% Last digit
insert2(T, Prev, [Digit], Value, Ref, Name) ->
    Num = to_hex_integer(lists:append(Prev, [Digit]), 0),
    case mnesia:dirty_read({T,{Ref, Name, Num}}) of
	[#number_analyser{num = _Key,res = get_more_digits}] ->
	    mnesia:write(T, #number_analyser{num = {Ref, Name, Num}, 
					     res = {get_more_digits,Value}},
			write);

	[#number_analyser{num = _Key,res = {get_more_digits,Value}}] ->
		mnesia:abort(prefix_already_defined);

	[#number_analyser{num = _Key,res = Value}] ->
		mnesia:abort(prefix_already_defined);

	[] ->
	    mnesia:write(T, #number_analyser{num = {Ref, Name, Num}, 
					     res = Value},
			write);
	X ->
	    io:format("~p~n",[X])
    end;
%% More digits exists
insert2(T, Prev, [Digit|Tail], Value, Ref, Name) ->
    Num = to_hex_integer(L = lists:append(Prev, [Digit]), 0),
    case mnesia:dirty_read({T,{Ref, Name, Num}}) of
	[#number_analyser{num = _Key,res = get_more_digits}] ->
	    insert2(T, L, Tail, Value, Ref, Name);
	[#number_analyser{num = _Key,res = {get_more_digits,_Val}}] ->
	    insert2(T, L, Tail, Value, Ref, Name);
	[#number_analyser{num = _Key,res = Val}] ->
	    mnesia:dirty_write(T, #number_analyser{num = {Ref, Name, Num},
						   res = {get_more_digits,Val}}),
	    insert2(T, L, Tail, Value, Ref, Name);
	[] ->
	    mnesia:dirty_write(T, #number_analyser{num = {Ref, Name, Num},
						   res = get_more_digits}),
	    insert2(T, L, Tail, Value, Ref, Name)
    end.

to_hex_integer(HexIntList) ->
    to_hex_integer(HexIntList, 0).

to_hex_integer([H|T], Ack) ->
    to_hex_integer(T, Ack*16 + H);
to_hex_integer([], Ack) -> 
    Ack.

process_numberlist([H|T]) ->
    [hex(H) | process_numberlist(T)];
process_numberlist([]) -> 
    [].

%% We make special case on zero so that we catch the 
%% case with phone numbers beginning with 0

hex(D) ->
    if
	1 =< D, D =<  9 -> D;
	D == 0           -> 16#a;
	D == 11          -> 16#b;
	D == 12          -> 16#c
    end.

%%--------------------------------------------------------------------
%% @spec list_info(T, Ref, Name) -> {User,TimeStamp} | {error, Reason}
%% @doc Gives information about the specified list.
%% @end
%%--------------------------------------------------------------------
list_info(T, Ref, Name) ->
    F = fun() -> mnesia:read({bw_lists,{T,Ref,Name}}) end,
    case mnesia:transaction(F) of
        {aborted, Reason} ->
            {error, Reason};
        {atomic, [M]} ->
            {M#bw_lists.username, M#bw_lists.timestamp}
    end.

%%
%% Print all phone numbers in table T
%%

%%--------------------------------------------------------------------
%% @spec print_all(Type, Ref, Name) -> Result | exit()
%% @doc This function returns an erlang list of all the Numberlists in the
%% bw_list referenced as printable ascii strings e.g. ["0181","0171"].
%% @end
%%--------------------------------------------------------------------
print_all(T, Ref, Name) ->
    print_all(T, mnesia:dirty_first(T), [], Ref, Name).

print_all(_T, '$end_of_table', Result, _Ref, _Name) -> 
    Result;
%%    lists:map(fun({A,_B}) -> A end, Result);

print_all(T, Key, Result, Ref, Name) ->
    print_all2(T, mnesia:dirty_read(T, Key), Result, Ref, Name).

print_all2(T, [#number_analyser{num = Key, res = get_more_digits}], Result, Ref, Name) ->
    print_all(T, mnesia:dirty_next(T, Key), Result, Ref, Name);

print_all2(T, [#number_analyser{num = {Ref, Name, Telno}, res = {get_more_digits,Value}}], Result, Ref, Name) ->
    print_all(T, mnesia:dirty_next(T, {Ref, Name, Telno}), 
	      [{digitlist_to_string(hex_to_phonenumber(Telno, [])), Value}|Result], Ref, Name);
print_all2(T, [#number_analyser{num = {Ref, Name, Telno}, res = Value}], Result, Ref, Name) ->
    print_all(T, mnesia:dirty_next(T, {Ref, Name, Telno}), 
	      [{digitlist_to_string(hex_to_phonenumber(Telno, [])), Value}|Result], Ref, Name);

print_all2(T, [#number_analyser{num = {R, N, Telno}}], Result, Ref, Name) ->
    print_all(T, mnesia:dirty_next(T, {R, N, Telno}), Result, Ref, Name).

hex_to_phonenumber(0, Ack) ->
    Ack;
hex_to_phonenumber(I, Ack) -> 
    hex_to_phonenumber(I div 16, [un_hex(I rem 16) | Ack]).

un_hex(16#a) -> 0;
un_hex(16#b) -> 11;
un_hex(16#c) -> 12;
un_hex(I) -> I.

digitlist_to_string(Ds) ->
    [digit_to_char(D) || D <- Ds].

digit_to_char(D) when D =< 9 ->
    $0+D.

%%--------------------------------------------------------------------
%% @spec debug_print(Type, Ref, Name) -> Result | exit()
%% @doc This function returns an erlang list of all the Numberlists in the
%% bw_list. The difference from the print_all/3 function is that this function
%% prints all of the intermediate entries in the search tree and the results
%% from the analysis. Entries are also returned as integer lists rather than
%% strings.
%% @end
%%--------------------------------------------------------------------
debug_print(T, Ref, Name) ->
    Entries = ets:match(T, {number_analyser,{Ref,Name,'$1'},'$2'}),
    List_entries = lists:map(fun([X,Y]) -> {hex_to_phonenumber(X,[]),Y} end, Entries),
    lists:sort(List_entries).

%% Try to look up a phone number 
try_lookup(_Table, _Ref, _Name, []) -> invalid;
try_lookup(_Table, _Ref, _Name, Number) -> 
    try_lookup(_Table, _Ref, _Name, Number,no_entry).

try_lookup(Table, Ref, Name, [H|T],Found) ->
    case lookup(H, Table, Ref, Name) of
	{get_more_digits, Sofar} ->
	    try_lookup1(Sofar, T, Table, Ref, Name,Found);
	{get_more_digits, Sofar, Value} ->
	    try_lookup1(Sofar, T, Table, Ref, Name, Value);
	Other -> Other
    end.

try_lookup1(Sofar, [H|T], Table, Ref, Name, Found) ->
    case lookup(Sofar, H, Table, Ref, Name) of
	{get_more_digits, Sofar2} ->
	    try_lookup1(Sofar2, T, Table, Ref, Name, Found);
	{get_more_digits, Sofar2, Value} ->
	    try_lookup1(Sofar2, T, Table, Ref, Name, Value);
	{found,Value} ->
	    Value;
	_Other -> Found
    end;
%% try_lookup1(_Sofar, [], _Table, _Ref, _Name, _Found) ->
%%     not_enough_digits;    
try_lookup1(_Sofar, [], _Table, _Ref, _Name, Found) ->
    Found.


lookup(FirstDigit, T, Ref, Name) ->
    lookup(0, FirstDigit, T, Ref, Name).

lookup(Prev, Dig, T, Ref, Name) ->
    D = (Prev * 16) + hex(Dig),
    case mnesia:dirty_read({T, {Ref, Name, D}}) of
	[#number_analyser{num = {Ref, Name, D},
			  res = get_more_digits}] -> 
	    {get_more_digits, D};
	[#number_analyser{num = {Ref, Name, D},
			  res = {get_more_digits, Val}}] -> 
	    {get_more_digits, D,Val};
	[#number_analyser{num = {Ref, Name, D}, 
			  res = Value}] -> 
	    {found, Value};
	[]       ->    
	    no_entry
    end.

%%--------------------------------------------------------------------
%% @spec mnesia_table() -> {atomic, ok} | {aborted, Reason}
%% @equiv mnesia_table([node()])
%% @doc Creates the table on the local node.
%% @end
%%--------------------------------------------------------------------
mnesia_table() ->
    mnesia_table([node()]).

%%--------------------------------------------------------------------
%% @spec mnesia_table(Nodes) -> {atomic, ok} | {aborted, Reason}
%% @doc This function is a one off requirement to set up the list management
%% mnesia table. If a list of node names is given as argument the table is
%% replicated on the given nodes.
%% @end
%%--------------------------------------------------------------------
mnesia_table(Nodes) ->
    mnesia:create_table(bw_lists,
                        [{attributes, record_info(fields, bw_lists)},
			 {type, set},
                         {disc_copies, Nodes}]).

get_tables(Record_name) ->
    get_tables(Record_name, mnesia:system_info(tables), []).
get_tables(Record_name, [Table|T], Result) ->
    case mnesia:table_info(Table, record_name) of
	Record_name ->
	    get_tables(Record_name, T, [Table|Result]);
	_ ->
	    get_tables(Record_name, T, Result)
    end;
get_tables(_Record_name, [], Result) ->
    Result.
