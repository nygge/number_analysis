%%%-------------------------------------------------------------------
%%% @copyright 1995 Claes Wikstrom (klacke@erix.eicsson.se)
%%% @author Claes Wikstrom <klacke@erix.eicsson.se>
%%% @author Sean Hinde <sean.hinde@gmail.com>
%%% @doc Provides a generic number analyser for dialled numbers.
%%% num_anal provides functions to create lists of phone numbers which may
%%% be analysed on on either a longest match or shortest match basis until
%%% either a match is made, a match is definitely not made, or no more digits
%%% are left. Each new list which is created is implemented using a single
%%% Mnesia table which may be replicated on a number of Erlang Nodes. 
%%%
%%% Within each new table multiple lists of numbers may be built indexed
%%% by a grouping called Ref. Functions are provided to create new tables,
%%% add entries to lists within the table, retrieve all lists contained in
%%% a table, retrieve all the phone numbers associated with a Ref within a
%%% table, as well as looking up and deleting entries. 
%%%
%%% There are three ways of looking up in the tables best illustrated by
%%% an example. e.g. if a table has the following two entries 
%%% <pre>
%%% [0,1,8,1] -> outer_london
%%% [0,1,8,1,2,1,4] -> one2one
%%% </pre>
%%% The functions give the following results: 
%%% <pre>
%%% check(Type, Ref, [0,1,8,1,2,1,4,2,4,1,3]) -> outer_london
%%% longest_match(Type, Ref, [0,1,8,1,2,1,4,2,4,1,3]) -> one2one
%%% exact_match(Type, Ref, [0,1,8,1,2,1,4,2,4,1,3]) -> no_match
%%% </pre>
%%%
%%% This module was posted on the erlang-questions mailing list
%%% [http://www.erlang.org/ml-archive/erlang-questions/200401/msg00009.html]
%%% by Sean Hinde.
%%%
%%% == Database Design ==
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

%%% === KNOWN BUGS ===
%%% Inserting an entry into the table which is a substring of an existing
%%% entry will leave a dangling tail in the analysis which may cause
%%% unexpected results.

-module(na_num_anal).
-export([new/1, new/2]).
-export([ranges/2, print_all/2, print_prefix/3, check/3, delete/3, insert/4]).
-export([delete_list/2, longest_match/3, exact_match/3]).
-export([print_match/3]).

%% @type number_analyser() = #number_analyser{num=Prefix::integer(),res=Result}
%% Result = get_more_digits | {get_more_digits, Value} | Value
%% Value = term().
-record(number_analyser, {num = [],
			  res = null}).

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
%% atom. e.g. Type could be b_num, for the b-number analysis lists for an
%% application. If a list of node names are specified, the table is
%% replicated on all those nodes, otherwise the table is created on the local
%% node only.
%% @end
%%--------------------------------------------------------------------
new(Type, Nodes) ->
    mnesia:create_table(Type,
                        [{attributes, record_info(fields, number_analyser)},
			 {record_name, number_analyser},
                         {disc_copies, Nodes}]).


%%--------------------------------------------------------------------
%% @spec check(Type, Ref, Numberlist) -> Result | no_match
%% @doc This function looks up a telephone number in the form
%% [0,1,8,1,2,1,4,2,4,1,3] digit by digit on a shortest match basis.
%% If no match is found returns no_match.
%% @end
%%--------------------------------------------------------------------
check(Type, Ref, Numberlist) ->
    case try_lookup(Type, Ref, Numberlist) of
	{found, Result} ->
	    Result;
	_ ->
	    no_match
    end.

%%--------------------------------------------------------------------
%% @spec longest_match(Type, Ref, Numberlist) ->  Result | no_match
%% @doc This function looks up a telephone number in the form
%% [0,1,8,1,2,1,4,2,4,1,3] digit by digit on a longest match basis.
%% If no match is found returns no_match.
%% @end
%%--------------------------------------------------------------------
longest_match(Type, Ref, Numberlist) ->
    case long_lookup(Type, Ref, Numberlist) of
	{found, Result} ->
	    Result;
	_ ->
	    no_match
    end.

%%--------------------------------------------------------------------
%% @spec exact_match(Type, Ref, Numberlist) -> Result | no_match
%% @doc This function looks up a telephone number in the form
%% [0,1,8,1,2,1,4,2,4,1,3] on an exact match basis.
%% If no match is found returns no_match.
%% @end
%%--------------------------------------------------------------------
exact_match(Type, Ref, Numberlist) ->
     F = fun() ->
		case mnesia:read(Type,{Ref, to_hex_integer(process_numberlist(Numberlist))}, read) of
		    [#number_analyser{res=get_more_digits}] ->
			mnesia:abort(number_has_no_result);
		    [#number_analyser{res=Result}] ->
			Result;
		    _ ->
			mnesia:abort(no_entry)
		end
	end,
    case mnesia:transaction(F) of
	{aborted, _Reason} ->
	    no_match;
	{atomic, Res} ->
	    Res
    end.

%% This is lazy. I just tag deleted entries with get_more_digits
%% so the tree still works if this was a sublist of another
%% entry. If this was the end of a tree then all the data is left hanging
%% around. messy, but pretty safe *** fixme ***
%%--------------------------------------------------------------------
%% @spec delete(T, Ref, NumList) ->ok | {error, Reason}
%% @doc This function attempts to delete the entry referenced.
%% If Numberlist is a prefix of a number already in the table this command
%% is rejected with Reason trying_to_delete_sublist.
%% @end
%%--------------------------------------------------------------------
delete(T, Ref, NumList) ->
    F = fun() ->
		case mnesia:read(T, {Ref, to_hex_integer(process_numberlist(NumList))}, read) of
		    [#number_analyser{res=get_more_digits}] ->
			mnesia:abort(trying_to_delete_sublist);
		    [] ->
			ok;
		    _ ->
			mnesia:write(T, #number_analyser{num = {Ref, to_hex_integer(process_numberlist(NumList))}, 
							 res = get_more_digits}, write)
		end
	end,
    case mnesia:transaction(F) of
	{aborted, Reason} ->
	    {error, Reason};
	{atomic, _} ->
	    ok
    end.
		

%%--------------------------------------------------------------------
%% @spec delete_list(T, Ref) -> ok | {error, Reason}
%% @doc This function attempts to delete all entries in table Type
%% referenced by Ref.
%% @end
%%--------------------------------------------------------------------
delete_list(T, Ref) ->
    WildPat = mnesia:table_info(T, wild_pattern),
    Pat = WildPat#number_analyser{num = {Ref, '_'}},
    F = fun() ->
		Entries = mnesia:match_object(T, Pat, read),
		lists:foreach(fun(X) ->
				      mnesia:delete_object(T, X, write)
			      end, Entries)
	end,
    case mnesia:transaction(F) of
	{aborted, Reason} ->
	    {error, Reason};
	{atomic, _} ->
	    ok
    end.

%%--------------------------------------------------------------------
%% @spec insert(T, Ref, NumberList, Value) -> ok | {error, Reason}
%% @doc This function attempts to insert the number Numberlist (given as
%% list e.g [0,1,8,1]) into table Type, List Ref, Name. Future matches
%% against this number by the check function will return the result Value.
%% If there is not already an entry against Ref it is created automatically.
%% @end
%%--------------------------------------------------------------------
insert(T, Ref, NumberList, Value) ->
    F = fun() ->
		insert2(T, [], process_numberlist(NumberList), Value, Ref)
	end,
    case mnesia:transaction(F) of
	{aborted, Reason} ->
	    {error, Reason};
	{atomic, _} ->
	    ok
    end.

insert2(T, Prev, [Digit|Tail], Value, Ref) ->
    Num = to_hex_integer(L = lists:append(Prev, [Digit]), 0),
    case Tail of
	[] -> 
	    mnesia:write(T, #number_analyser{num = {Ref, Num}, 
					     res = Value}, write);	    
	_ -> 
	    case mnesia:read(T, {Ref, Num}, read) of
		[#number_analyser{res = get_more_digits}] -> 
		    insert2(T, L, Tail, Value, Ref); % Already in the database
		[#number_analyser{res = _Some_value}] -> 
		    insert2(T, L, Tail, Value, Ref); % Already in the database, don't want to overwrite result
		[]       ->    
		    mnesia:write(T, #number_analyser{num = {Ref, Num}, 
						     res = get_more_digits}, write),
		    insert2(T, L, Tail, Value, Ref)
	    end
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

print_match(T, Ref, RecPat) ->
    WildPat = mnesia:table_info(T, wild_pattern),
    Pat = WildPat#number_analyser{num = {Ref, '_'}, res = RecPat},
    F = fun() ->
                mnesia:match_object(T, Pat, read)
	end,
    case mnesia:transaction(F) of
	{aborted, Reason} ->
	    {error, Reason};
	{atomic, List} ->
            format_numbers(List)
    end.

format_numbers(List) ->
    format_numbers(List, []).
 
format_numbers([#number_analyser{num = {_R, Number}, res = Value}|List], NewList) ->
    format_numbers(List, [NewList,{number:digitlist_to_string(hex_to_phonenumber(Number, [])), Value}]);
format_numbers([], NewList) ->
    lists:flatten([NewList]).
    

%%--------------------------------------------------------------------
%% @spec ranges(T, Ref) -> integer() | exit()
%% @doc Get number of ranges with Ref.
%% @end
%%--------------------------------------------------------------------
ranges(T, Ref) ->
    Pat = [{#number_analyser{num={Ref,'_'},res='$1'},[{'=/=','$1',get_more_digits}],[1]}],
    F = fun () ->
		length(mnesia:select(T,Pat))
	end,
     {atomic, Res} = mnesia:transaction(F),
    Res.


%%
%% Print all phone numbers in table T with ref Ref
%%

%%--------------------------------------------------------------------
%% @spec print_all(T, Ref) -> Result | exit()
%% @doc This function returns an erlang list of all {Numberlist, Value}
%% in List Ref e.g. 
%% <pre>
%% [{[0,1,8,1], outer_london},
%%  {[0,1,7,1], inner_london}]
%% </pre>
%% @end
%%--------------------------------------------------------------------
print_all(T, Ref) ->
    print_all(T, mnesia:dirty_first(T), [], Ref).

print_all(_T, '$end_of_table', Result, _Ref) -> 
    Result;
print_all(T, Key, Result, Ref) ->
    print_all2(T, mnesia:dirty_read(T, Key), Result, Ref).

print_all2(T, [#number_analyser{num = Key, res = get_more_digits}], Result, Ref) ->
    print_all(T, mnesia:dirty_next(T, Key), Result, Ref);
print_all2(T, [#number_analyser{num = {Ref, Telno}, res = Value}], Result, Ref) ->
    print_all(T, mnesia:dirty_next(T, {Ref, Telno}), 
	      [{number:digitlist_to_string(hex_to_phonenumber(Telno, [])), Value}|Result], Ref);
print_all2(T, [#number_analyser{num = {R, Telno}}], Result, Ref) ->
    print_all(T, mnesia:dirty_next(T, {R, Telno}), Result, Ref).

%%--------------------------------------------------------------------
%% @spec print_prefix(T, Ref, Prefix) -> Result | exit()
%% @doc This function returns an erlang list of all {Numberlist, Value}
%% in List Ref where Prefix is a prefix of Numberlist e.g. 
%% <pre>
%% [{[0,1,8,1], outer_london},
%%  {[0,1,7,1], inner_london}]
%% </pre>
%% @end
%%--------------------------------------------------------------------
print_prefix(T, Ref, Prefix) ->
    print_prefix(T, mnesia:dirty_first(T), [], Ref, Prefix).

print_prefix(_T, '$end_of_table', Result, _Ref, _Prefix) -> 
    Result;
print_prefix(T, Key, Result, Ref, Prefix) ->
    print_prefix2(T, mnesia:dirty_read(T, Key), Result, Ref, Prefix).

print_prefix2(T, [#number_analyser{num = Key, res = get_more_digits}], Result, Ref, Prefix) ->
    print_prefix(T, mnesia:dirty_next(T, Key), Result, Ref, Prefix);
print_prefix2(T, [#number_analyser{num = {Ref, Telno}=Key, res = Value}], Result, Ref, Prefix) ->
    Number = number:digitlist_to_string(hex_to_phonenumber(Telno, [])),
    case lists:prefix(Prefix, Number) of
	true ->
	    print_prefix(T, mnesia:dirty_next(T, {Ref, Telno}), [{Number, Value}|Result],
			 Ref, Prefix);
	false ->
	    print_prefix(T, mnesia:dirty_next(T, Key), Result, Ref, Prefix)
    end;
print_prefix2(T, [#number_analyser{num = {R, Telno}}], Result, Ref, Prefix) ->
    print_prefix(T, mnesia:dirty_next(T, {R, Telno}), Result, Ref, Prefix).

hex_to_phonenumber(0, Ack) ->
    Ack;
hex_to_phonenumber(I, Ack) -> 
    hex_to_phonenumber(I div 16, [un_hex(I rem 16) | Ack]).

un_hex(16#a) -> 0;
un_hex(16#b) -> 11;
un_hex(16#c) -> 12;
un_hex(I) -> I.



%% Try to look up a phone number 
try_lookup(_Table, _Ref, []) -> invalid;
try_lookup(Table, Ref, [H|T]) ->
    case lookup(H, Table, Ref) of
	{get_more_digits, Sofar} ->
	    try_lookup(Sofar, T, Table, Ref);
	{found, Result, _} ->
	    {found, Result};
	Other -> Other
    end.

try_lookup(Sofar, [H|T], Table, Ref) ->
    case lookup(Sofar, H, Table, Ref) of
	{get_more_digits, Sofar2} ->
	    try_lookup(Sofar2, T, Table, Ref);
	{found, Result, _} ->
	    {found, Result};
	Other -> Other
    end;
try_lookup(_Sofar, [], _Table, _Ref) ->
    not_enough_digits.

%% Try to look up a phone number looking for the longest match rather
%% than the first match.
long_lookup(_Table, _Ref, []) -> invalid;
long_lookup(Table, Ref, [H|T]) ->
    case lookup(H, Table, Ref) of
	{get_more_digits, Sofar} ->
	    long_lookup(Sofar, T, Table, Ref, no_entry);
	{found, Value, Sofar} ->
	    long_lookup(Sofar, T, Table, Ref, {found, Value});
	Other -> Other
    end.

long_lookup(Sofar, [H|T], Table, Ref, Result) ->
    case lookup(Sofar, H, Table, Ref) of
	{get_more_digits, Sofar2} ->
	    long_lookup(Sofar2, T, Table, Ref, Result);
	{found, Value, Sofar2} ->
	    long_lookup(Sofar2, T, Table, Ref, {found, Value});
	no_entry ->
	    Result
    end;
long_lookup(_Sofar, [], _Table, _Ref, Result) ->
    Result.



lookup(FirstDigit, T, Ref) ->
    lookup(0, FirstDigit, T, Ref).

lookup(Prev, Dig, T, Ref) ->
    D = (Prev * 16) + hex(Dig),
    case mnesia:dirty_read({T, {Ref, D}}) of
	[#number_analyser{num = {Ref, D},
			  res = get_more_digits}] -> 
	    {get_more_digits, D};
	[#number_analyser{num = {Ref, D}, 
			  res = Value}] -> 
	    {found, Value, D};
	[]       ->    
	    no_entry
    end.

