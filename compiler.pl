%:- dynamic lex/2, deletable/1, chain_star/2, lc_star/2, predict/6.
%word(_,_).
%add_fact(+fact)
add_fact(Fact) :-
    retract(Fact),
    assertz(Fact).
add_fact(Fact) :-
    assertz(Fact).

% precompile_grammar(+filename)
precompile_grammar(Filename) :-
    retractall(lex),
    retractall(deletable),
    retractall(chain_star),
    retractall(lc_star),
    retractall(predict),
    current_output(StdOut),
    consult(Filename),
    print('Computing lexicon ... '),
    flush_output,
    compute_lexicon,
    print('done'),nl,
    print('Computing deletables ... '),
    flush_output,
    compute_deletable,
    print('done'),nl,
    print('Computing chain relation ... '),
    flush_output,
    compute_chain,
    print('done'),nl,
    print('Computing left corner relation ... '),
    flush_output,
    compute_lc_star,
    print('done'),nl,
    print('Computing predictions ... '),
    flush_output,
    compute_predict,
    print('done'),nl,
    % Get new filename
    file_name_extension(Base,_Ext,Filename),
    file_name_extension(Base,'pcg.pl',NewFile),
    format('Writing to file ~w ...~n', [NewFile]),
    tell(NewFile),
    % Do the writing
    startsymbol(S),
    format(StdOut,'Writing startsymbol ...~n',[]), flush_output,
    forall(startsymbol(S),format('startsymbol(~w).~n',S)),
    format(StdOut,'Writing lexicon ...~n',[]), flush_output,
    forall(lex(Cat,Word),format('lex(~w,~p).~n',[Cat,Word])),
    format(StdOut,'Writing deletable symbols ...~n',[]), flush_output,
    forall(deletable(D),format('deletable(~w).~n',[D])),
    format(StdOut,'Writing chain relation ...~n',[]), flush_output,
    forall(chain_star(A,B),format('chain(~w,~w).~n',[A,B])),
    format(StdOut,'Writing left corner relation ...~n',[]), flush_output,
    forall(lc_star(B,A),format('lc_star(~w,~w).~n',[B,A])),
    format(StdOut,'Writing predictions ...~n',[]), flush_output,
    forall(predict(E,D,Cc,A,AlphaBBeta,CGamma),format('predicted(~w,~w,~w,~w,~p,~p).~n',[E,D,Cc,A,AlphaBBeta,CGamma])),
    told,
    print('done'),nl
    .

compute_lexicon :-
    bagof([Cat,Word],lexp(Cat,Word),LexList),
    list_to_set(LexList,Lex),
    forall(member([Cat,Word],Lex),add_fact(lex(Cat,Word))).

compute_deletable :-
    bagof(D,deletablep(D),DelList),
    list_to_set(DelList,Del),
    forall(member(D,Del),add_fact(deletable(D))).
    
compute_chain :-
    bagof([A,B],chain_starp(A,B),ChainList),
    list_to_set(ChainList,Chain),
    forall(member([A,B],Chain),add_fact(chain_star(A,B))).

compute_lc_star :-
    bagof([B,A],lc_starp(B,A),LCStarList),
    list_to_set(LCStarList,LCStar),
    forall(member([B,A],LCStar),add_fact(lc_star(B,A))).

compute_predict :-
    bagof([E,D,Cc,A,AlphaBBeta,CGamma],predictp(E,D,Cc,A,AlphaBBeta,CGamma),PredictList),
    list_to_set(PredictList,Predict),
    forall(member([E,D,Cc,A,AlphaBBeta,CGamma],Predict),add_fact(predict(E,D,Cc,A,AlphaBBeta,CGamma))).

tuple_to_list([],[]):-!.
tuple_to_list((A,B),[A|C]) :- tuple_to_list(B,C),!.
tuple_to_list([A|B],[A|B]):-!.
tuple_to_list(A,[A]):-!.

non_terminalp(A) :- (A --> _).
non_terminalp(A) :- current_predicate(word/2), word(_,A).
lexp(Cat,Word) :- 
    (Cat --> Word),
    Word=[W|_Ord],
    integer(W).
lexp(Cat,Word) :-
    current_predicate(word/2),
    word(Word,Cat),
    Word=[W|_Ord],
    integer(W).


deletablep([]) :- 
    false.

deletablep(NonTerm) :- 
    (NonTerm --> [])
    .
deletablep(NonTerm) :-
    current_predicate(word/2),
    word([],NonTerm)
    .

deletablep(NonTerm) :-
    (NonTerm --> Rhs),
    tuple_to_list(Rhs,RhsL),
    forall(member(X,RhsL),deletablep(X))
    .
    
chainp(A,B) :-
    (A --> Rhs),
    tuple_to_list(Rhs,RhsL),
    append(Alpha,[B|Beta],RhsL),
    non_terminalp(B),
    forall(member(X,Alpha),deletable(X)),
    forall(member(Y,Beta),deletable(Y))
    .

chain_plusp(A,B) :-
    chainp(A,B).

chain_plusp(A,B) :- 
    non_terminalp(C),
    chainp(A,C),
    chainp(C,B)
    .

chain_starp(A,B) :-
    chain_plusp(A,B).

chain_starp(A,A) :- non_terminalp(A).

lcp(B,A) :-
    (A --> Rhs),
    tuple_to_list(Rhs,RhsL),
    non_terminalp(B),
    append(Alpha,[B|_],RhsL),
    forall(member(X,Alpha),deletable(X))
    .

lcp(B,A) :-
    lexp(A,B).

lc_plusp(B,A) :- 
    lcp(B,A).

lc_plusp(B,A) :-
    lcp(B,C),
    non_terminalp(C),
    lcp(C,A)
    .

lc_starp(A,A) :- lc_plusp(A,_); lc_plusp(_,A).

lc_starp(A,B) :- lc_plusp(A,B).

predictp(E,D,Cc,A,AlphaBBeta,[C|Gamma]) :-
    lex(_,Cc),
    lc_star(Cc,C),
    chain_star(B,D),
    lc_star(A,E),
    non_terminalp(A),
    non_terminalp(B),
    non_terminalp(C),
    non_terminalp(D),
    non_terminalp(E),
    (A --> Rhs),
    tuple_to_list(Rhs,RhsL),
    append(AlphaBBeta,[C|Gamma],RhsL),
    append(Alpha,[B|Beta],AlphaBBeta),
    forall(member(X,Alpha),deletable(X)),
    forall(member(Y,Beta),deletable(Y))
    .
