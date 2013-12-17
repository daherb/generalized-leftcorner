:- dynamic expected/2, ctree/4, ptree/5.
% defined as:
% ctree(From, To, A, AlphaBBeta)
% ptree(From, To, A, AlphaBBeta, CGamma)

% Uncomment for debug output:
% debug_print.

load_grammar(Grammar) :-
    consult(Grammar).

parse(Sentence,Result) :-
    tokenize(Sentence,WordList),
    leftcorner(WordList,Result)
    .

parse(Sentence) :-
    parse(Sentence,Result),
    (Result -> print('The sentence is parseable'),!;
     print('The sencence cannot be parsed')),nl
    .

parse :-
    read_sentence(Sentence),
    parse(Sentence).

read_sentence(SentList) :-
    print('Bitte Satz eingeben:'),nl,
    print('||: '),
    current_input(In),
    read_line_to_codes(In,Codes),
    char_code('.',Dot),!,
    append(SentList,[Dot|_Rest],Codes),
    !
    .

tokenize(SentList,WordList) :-
    char_code(' ',Spc),
    append(CharList,[Spc|Rest],SentList),!,
    tokenize(Rest,[CharList],RevWordList),
    reverse(RevWordList,WordList)
    .

tokenize(SentList, Accumulator,RevWordList) :-
    char_code(' ',Spc),
    append(CharList,[Spc|Rest],SentList),!,
    tokenize(Rest,[CharList|Accumulator],RevWordList)
    .

tokenize(SentList, Accumulator,RevWordList) :-
    char_code(' ',Spc),
    \+(member(Spc,SentList)),
    RevWordList=[SentList|Accumulator]
    .

% Just returns true if a complete tree for the sentence
% was found. Can be Extended to build complete parse tree
build_result(StartCat,StartPos,EndPos,true) :-
    ctree(StartPos,EndPos,StartCat,_Alpha),!.

build_result(_StartCat,_StartPos,_EndPos,false).

add_fact(Tree) :- 
    retract(Tree),
    assertz(Tree),!
    .

add_fact(Tree) :- 
    assertz(Tree)
    .

clear :-
    %retractall(ctree),
    %retractall(ptree),
    %retractall(expected),
    (forall(ctree(I,J,A,Alpha),retract(ctree(I,J,A,Alpha))); true),
    (forall(ptree(I,J,A,AlphaBBeta,CGamma),retract(ptree(I,J,A,AlphaBBeta,CGamma)));true),
    (forall(expected(Pos,Cat),retract(expected(Pos,Cat))); true)
    .
leftcorner(WordList,Result) :-
    % Clean up everything
    clear,
    length(WordList,EndPos),
    (current_predicate(debug_print/0),print('start'),nl,listing(expected),nl;true),
    start,
    (leftcorner(WordList,0,EndPos); true),
    startsymbol(S),
    build_result(S,0,EndPos,Result),!
    .

% Reached End of parse
leftcorner(_,End,End) :-
    (current_predicate(debug_print/0),print('complete1'),nl,listing(ctree),nl;true),
    complete1
    .

leftcorner(WordList,Pos,End) :-
    (current_predicate(debug_print/0),print('scan'),nl,listing(ctree),nl;true),
    scan(WordList,Pos,NPos,Rest),
    (current_predicate(debug_print/0),print('complete1'),nl,listing(ctree),nl;true),
    complete1,
    (current_predicate(debug_print/0),print('complete2'),nl,listing(ptree),nl;true),
    complete2(Rest,End),
    (current_predicate(debug_print/0),print('predict'),nl,listing(ptree),nl;true),
    predict(Rest),
    (current_predicate(debug_print/0),print('expect'),nl,listing(expected),nl;true),
    expect,
    leftcorner(Rest,NPos,End)
    .

start :-
    startsymbol(S),
    add_fact(expected(0,S))
    .

scan([],_,_,[]).
scan(WordList,I,J,Rest) :-
    WordList=[Word|Rest],
    J is I+1,
    lex(Cat,Word),
    add_fact(ctree(I,J,Cat,Word)),
    (current_predicate(debug_print/0),print('scan'),nl,listing(ctree),nl;true),
    false
    .
scan(WordList,I,J,Rest) :-
    WordList=[Word|Rest],
    J is I+1,
    lex(_Cat,Word).

expect :-
    ptree(_I,J,_A,_Alpha,[B|_Beta]),
    add_fact(expected(J,B)),
    (current_predicate(debug_print/0),print('expect'),nl,listing(expected),nl;true),
    false.
expect.

predict([NextWord|_Rest]) :-
    expected(I,E),
    ctree(I,J,D,_Delta),
    predicted(E,D,NextWord,A,AlphaBBeta,CGamma),
    add_fact(ptree(I,J,A,AlphaBBeta,CGamma)),
    (current_predicate(debug_print/0),print('predict'),nl,listing(ptree),nl;true),
    false
    .
predict(_).

complete1 :-
    chain(B,D),
    ptree(I,K,A,Alpha,[B|Beta]),
    ctree(K,J,D,_Delta),
    forall(member(X,Beta),deletable(X)),
    append(Alpha,[B|Beta],AlphaBBeta),
    add_fact(ctree(I,J,A,AlphaBBeta)),
    (current_predicate(debug_print/0),print('complete1'),nl,listing(ctree),nl;true),
    false
    .
complete1.

complete2([NextWord|_Rest],End) :-
    chain(B,D),
    ptree(I,K,A,Alpha,[B|BetaCGamma]),
    append(Beta,[C|Gamma],BetaCGamma),
    ctree(K,J,D,_Delta),
    forall(member(X,Beta),deletable(X)),
    J<End,
    lc_star(NextWord,C),
    append(Alpha,[B|Beta],AlphaBBeta),
    add_fact(ptree(I,J,A,AlphaBBeta,[C|Gamma])),
    (current_predicate(debug_print/0),print('complete2'),nl,listing(ctree),nl;true),
    false
    .
complete2(_,_).
