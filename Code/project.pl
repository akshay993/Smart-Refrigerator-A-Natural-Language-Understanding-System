
% ===========================================================
% Main loop:
% 1. Repeat "input-response" cycle until input starts with "bye"
%    Each "input-response" cycle consists of:
% 		1.1 Reading an input string and convert it to a tokenized list
% 		1.2 Processing tokenized list
% ===========================================================

chat:-
 repeat,
   readinput(Input),
   process(Input),
  (Input = [bye| _] ),!.


% ===========================================================
% Read input:
% 1. Read char string from keyboard.
% 2. Convert char string to atom char list.
% 3. Convert char list to lower case.
% 4. Tokenize (based on spaces).
% ===========================================================

readinput(TokenList):-
   read_line_to_codes(user_input,InputString),
   string_to_atom(InputString,CharList),
   string_lower(CharList,LoweredCharList),
   tokenize_atom(LoweredCharList,TokenList).


% ===========================================================
%  Process tokenized input
% 1. Parse morphology and syntax, to obtain semantic representation
% 2. Evaluate input in the model
% If input starts with "bye" terminate.
% ===========================================================

process(Input):-
	parse(Input,SemanticRepresentation),
	modelchecker(SemanticRepresentation,Evaluation),
	respond(Evaluation),!,
	nl,nl.

process([bye|_]):-
   write('> bye!').


% ===========================================================
%  Parse:
% 1. Morphologically parse each token and tag it.
% 2. Add semantic representation to each tagged token
% 3. Obtain FOL representation for input sentence
% ===========================================================

%parse(Input, SemanticRepresentation):-
% ...

%% Added temporary SR parser

sr_parse(Sentence,M):-
        srparse([],Sentence,M).

%srparse([X],[],[X]):-numbervars(X,0,_).
srparse([X],[],[X]).


srparse([Z,Y,X|MoreStack],Words,M):-
      rule(LHS,[X,Y,Z]),
      srparse([LHS|MoreStack],Words,M).

srparse([Z,Y,X|MoreStack],Words,M):-
      rule(LHS,[X,Y]),
      srparse([Z,LHS|MoreStack],Words,M).


srparse([Y,X|MoreStack],Words,M):-
       rule(LHS,[X,Y]),
       srparse([LHS|MoreStack],Words,M).

srparse([X|MoreStack],Words,M):-
       rule(LHS,[X]),
       srparse([LHS|MoreStack],Words,M).



srparse(Stack,[Word|Words],M):-
        lex(X,Word),
        srparse([X|Stack],Words,M).

%% End of parser

% ===========================================================
% Grammar
% 1. List of lemmas
% 2. Lexical items
% 3. Phrasal rules
% ===========================================================

% --------------------------------------------------------------------
% Lemmas are uninflected, except for irregular inflection
% lemma(+Lemma,+Category)
% --------------------------------------------------------------------


lemma(is,be).
lemma(was,be).
lemma(are,be).


%%%%%%%%%% ------------ My Lemmas [Akshay Chopra]

%% Determiners
lemma(a,dtexists).
lemma(an,dtexists).
lemma(the,dtexists).
lemma(some,dtexists).
lemma(no,dtnotexists).
lemma(each,dtforall).
lemma(all,dtforall).
lemma(every,dtforall).

%% Numerals
lemma(one,dt).
lemma(two,dt).
lemma(three,dt).
lemma(four,dt).
lemma(five,dt).
lemma(six,dt).
lemma(seven,dt).
lemma(eight,dt).
lemma(nine,dt).
lemma(ten,dt).

%% Nouns
lemma(egg,n).
lemma(shelf,n).
lemma(fridge,n).
lemma(container,n).
lemma(sandwich,n).
lemma(meat,n).
lemma(tofu,n).
lemma(apple,n).
lemma(ham,n).
lemma(vegetable,n).
lemma(banana,n).
lemma(watermelon,n).
lemma(almond,n).
lemma(milk,n).
lemma(popsicle,n).
lemma(can,n).
lemma(skim,n).
lemma(box,n).

%% Proper Nouns
lemma(tom,pn).
lemma(mia,pn).
lemma(sam,pn).

%% Adjectives
lemma(blue,adj).
lemma(yellow,adj).
lemma(white,adj).
lemma(green,adj).
lemma(top,adj).
lemma(middle,adj).
lemma(bottom,adj).
lemma(red,adj).
lemma(empty,adj).

%% Verbs
lemma(expire,iv).
lemma(drink,tv).
lemma(drank,tv).
lemma(drunk,tv).
lemma(contain,tv).
lemma(eat,tv).
lemma(ate,tv).

%% Prepositions
lemma(in,p).
lemma(inside,p).
lemma(under,p).
lemma(with,p).
lemma(on,vacp).
lemma(to,vacp).

%% Relative Clauses
%% lemma(that,rel).
%% lemma(there,rel).


%% Auxilary Verbs (be)
lemma(were,be).
lemma(will,be).
lemma(did,be).
lemma(have,be).
lemma(had,be).
lemma(do,be).
lemma(did,be).

%% WHPR
lemma(who,whpr).
lemma(what,whpr).


%%%%%%%%%% ------------ End My Lemmas [Akshay Chopra]


% --------------------------------------------------------------------
% Constructing lexical items:
% word = lemma + suffix (for "suffix" of size 0 or bigger)
% --------------------------------------------------------------------



%%%%%%%%%% ------------ Lexicons


lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Word):- lemma(Word,dtforall),!.
lex(dt((X^P)^(X^Q)^exists(X,and(P,Q))),Word):-lemma(Word,dtexists),!.
lex(dt((X^P)^(X^Q)^not(exists(X,P^Q))), Word):-lemma(Word,dtnotexists),!.
lex(n(X^P),Word):- lemma(Word,n), P =.. [Word,X],!.
lex(pn((Word^X)^X),Word):- lemma(Word,pn),!.
lex(iv(X^P,[]),Word):-lemma(Word,iv), P=.. [Word,X],!.
lex(tv(K^W^P,[]),Word):-lemma(Word,tv), P=.. [Word,K,W],!.
lex(adj((X^P)^X^and(P,Q)),Word):-lemma(Word,adj), Q=.. [Word,X],!.
lex(p((Y^Z)^Q^(X^P)^and(P,Q)),Word):- lemma(Word,p), Z=.. [Word,X,Y],!.
lex(p((Y^Z)^Q^(X^P)^and(P,Q)),Word):- lemma(Word,vacp), Z=.. [Word,X,Y],!.
lex(whpr((X^P)^q(X,and(P,person))),who):- lemma(who,whpr).
lex(whpr((X^P)^q(X,and(P,thing))),what):- lemma(what,whpr).


%%%%%%%%%% ------------ Lexicons

%%%%%%%%%% ------------ Lexicons with inflections

lex(iv(X^P,[]),Y):-lemma(Word,iv),atom_concat(Word,d,Y),P=.. [Word,X],!.
lex(iv(X^P,[]),Y):-lemma(Word,iv),atom_concat(Word,ed,Y),P=.. [Word,X],!.
lex(iv(X^P,[]),Y):-lemma(Word,iv),atom_concat(Word,ing,Y),P=.. [Word,X],!.
lex(iv(X^P,[]),Y):-lemma(Word,iv),atom_concat(Temp,e,Word),sub_atom(Y,_,_,_,Temp),atom_concat(Temp,ing,Y),P=.. [Word,X],!.
lex(iv(X^P,[]),Y):-lemma(Word,iv),atom_concat(Word,s,Y),P=.. [Word,X],!.


lex(tv(K^W^P,[]),Y):-lemma(Word,tv),atom_concat(Word,d,Y), P=.. [Word,K,W],!.
lex(tv(K^W^P,[]),Y):-lemma(Word,tv),atom_concat(Word,ed,Y), P=.. [Word,K,W],!.
lex(tv(K^W^P,[]),Y):-lemma(Word,tv),atom_concat(Word,ing,Y), P=.. [Word,K,W],!.
lex(tv(K^W^P,[]),Y):-lemma(Word,tv),atom_concat(Temp,e,Word),sub_atom(Y,_,_,_,Temp),atom_concat(Temp,ing,Y),P=.. [Word,K,W],!.
lex(tv(K^W^P,[]),Y):-lemma(Word,tv),atom_concat(Word,s,Y), P=.. [Word,K,W],!.


lex(n(X^P),Y):- lemma(Word,n),atom_concat(Word,s,Y), P =.. [Word,X],!.
lex(n(X^P),Y):- lemma(Word,n),atom_concat(Word,es,Y), P =.. [Word,X],!.

%% Lexicon for Auxilary Verb
lex(be,Word) :- lemma(Word,be).

%%%%%%%%%% ------------ End Lexicons with inflections


% ...

% --------------------------------------------------------------------
% Suffix types
% --------------------------------------------------------------------

% ...

% --------------------------------------------------------------------
% Phrasal rules
% rule(+LHS,+ListOfRHS)
% --------------------------------------------------------------------

%%%%%%%%%% ------------ Shubham's Rules

rule(np(Y),[dt(X^Y),n(X)]).
rule(np(X),[pn(X)]).
rule(np(X),[n(X)]).
rule(n(A^C),[n(A^B),pp((A^B)^C)]).
rule(n(A),[adj(B^A),n(B)]).
rule(pp(C),[p(A^B^C),np(A^B)]).
rule(vp(A^B,[]),[tv(A^C,[]),np(C^B)]).
rule(s(B,[]),[np(A^B),vp(A,[])]).

rule(iv(X,[WH]),[tv(X^WH,[])]).
rule(vp(X^K,[]),[tv(X^Y,[]),np(Y^K)]).
rule(vp(X,WH),[iv(X,WH)]).
rule(s(X,WH),[vp(X,WH)]).
rule(ynq(Y),[be, np(X^Y),vp(X,[])]).
rule(ynq(Y),[be, np(X^Y),np(X)]).
rule(ynq(Y),[be, np(X^Y),pp(X)]).
rule(Y,[whpr(X^Y),vp(X,[])]).
rule(Y,[whpr(X^Y),be,pp(X)]).
rule(Z,[whpr((X^Y)^Z), inv_s(Y,[X])]).
rule(inv_s(Y,[WH]),[aux, np(X^Y),vp(X,[WH])]).


%%%%%%%%%% ------------ End of Shubham's Rules
% ...


% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================

% model(...,...)

% ===========================================================
%  Respond
%  For each input type, react appropriately.
% ===========================================================

% Declarative true in the model
respond(Evaluation) :-
		Evaluation = [true_in_the_model],
		write('That is correct'),!.

% Declarative false in the model
respond(Evaluation) :-
		Evaluation = [not_true_in_the_model],
		write('That is not correct'),!.

% Yes-No interrogative true in the model
respond(Evaluation) :-
		Evaluation = [yes_to_question],
		write('yes').

% Yes-No interrogative false in the model
respond(Evaluation) :-
		Evaluation = [no_to_question],
		write('no').

% wh-interrogative true in the model
% ...

% wh-interrogative false in the model
% ...
