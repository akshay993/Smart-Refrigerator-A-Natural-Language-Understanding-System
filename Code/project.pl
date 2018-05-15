
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

%% Added SR parser

parse(Sentence,M):-
        srparse([],Sentence,M).

srparse([X],[],[X]).

srparse([Z,Y,X|MoreStack],Words,M):-
      rule(LHS,[X,Y,Z]),
      srparse([LHS|MoreStack],Words,M).

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


%%%%%%%%%% ------------ Lemmas

%% Determiners
lemma(a,dtexists).
lemma(an,dtexists).
lemma(any,dtexists).
lemma(the,dtexists).
lemma(some,dtexists).
lemma(no,dtnotexists).
lemma(each,dtforall).
lemma(all,dtforall).
lemma(every,dtforall).

%% Numerals
lemma(one,one).
lemma(two,two).
lemma(three,three).
lemma(four,four).
lemma(five,five).
lemma(six,six).
lemma(seven,seven).
lemma(eight,eight).
lemma(nine,nine).
lemma(ten,ten).

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
lemma(bowl,n).
lemma(vegetable,n).
lemma(banana,n).
lemma(watermelon,n).
lemma(almond,n).
lemma(milk,n).
lemma(popsicle,n).
lemma(can,n).
lemma(box,n).
lemma(tomato,n).
lemma(onion,n).
lemma(carrot,n).
lemma(spinach,n).
lemma(orange,n).
lemma(apple,n).
lemma(mango,n).
lemma(chicken,n).
lemma(sausage,n).
lemma(steak,n).
lemma(fruit,n).
lemma(vegetable,n).
lemma(icecream,n).
lemma(freezer,n).

%% Proper Nouns
lemma(tom,pn).
lemma(mia,pn).
lemma(sam,pn).
lemma(sue,pn).

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
lemma(skim,adj).
lemma(almond,adj).


%% Verbs
lemma(expire,iv).
lemma(drink,tv).
lemma(drank,tv).
lemma(drunk,tv).
lemma(contain,tv).
lemma(have,tv).
lemma(had,tv).
lemma(has,tv).
lemma(eat,tv).
lemma(ate,tv).
lemma(took,tv).
lemma(take,tv).
lemma(put,dtv).
lemma(belong,tv).

%% Prepositions
lemma(in,p).
lemma(inside,p).
lemma(under,p).
lemma(with,p).
lemma(on,vacp).
lemma(on,p).
lemma(to,vacp).
lemma(of,p).
lemma(from,p).

%% Relative Clauses
lemma(that,rel).
lemma(which,rel).
lemma(who,rel).


%% Auxilary Verbs (be)
lemma(were,be).
lemma(will,be).
lemma(has,be).
lemma(had,be).
lemma(have,be).
lemma(did,be).
lemma(do,be).
lemma(is,be).
lemma(was,be).
lemma(are,be).

%% WHPR
lemma(who,whpr).
lemma(what,whpr).

%%%%%%%%%% ------------ End Lemmas


%% Hypernyms

isa(chicken,meat).
isa(ham,meat).
isa(sausage,meat).
isa(steak,meat).
isa(watermelon,fruit).
isa(banana,fruit).
isa(apple,fruit).
isa(mango,fruit).
isa(orange,fruit).
isa(tomato,vegetable).
isa(onion,vegetable).
isa(carrot,vegetable).
isa(spinach,vegetable).



% --------------------------------------------------------------------
% Constructing lexical items:
% word = lemma + suffix (for "suffix" of size 0 or bigger)
% --------------------------------------------------------------------



%%%%%%%%%% ------------ Lexicons

%DT_ForAll
lex(dt((X^P)^(X^Q)^forall(X,imp(P,Q))),Word):- lemma(Word,dtforall).

%DT_Exists
lex(dt((X^P)^(X^Q)^exists(X,and(P,Q))),Word):-lemma(Word,dtexists).

%DT_NotExisits
lex(dt((X^P)^(X^Q)^not(exists(X,and(P,Q)))), Word):-lemma(Word,dtnotexists).

%Noun
lex(n(X^P),Word):- lemma(Word,n), P =.. [Word,X].

%Proper_Noun
lex(pn((Word^X)^X),Word):- lemma(Word,pn).

%Intransitive_Verb
lex(iv(X^P,[]),Word):-lemma(Word,iv), P=.. [Word,X].

%Transitive_Verb
lex(tv(K^W^P,[]),Word):-lemma(Word,tv), P=.. [Word,K,W].

%Ditransitive_Verb
lex(dtv(K^W^P^R,[]),Word):-lemma(Word,dtv), R=.. [Word,K,W,P].

%Adjective
lex(adj((X^P)^X^and(P,Q)),Word):-lemma(Word,adj), Q=.. [Word,X].

%Preposition
lex(p2(K^W^P),Word):-lemma(Word,p), P=.. [Word,K,W].
lex(p1((Y^Z)^Q^(X^P)^and(P,Q)),Word):- lemma(Word,p), Z=.. [Word,X,Y].

%WHPR
lex(whpr((X^Z)^q(X,and(person(X),Z))),who):- lemma(who,whpr).
lex(whpr((X^Z)^q(X,and(thing(X),Z))),what):- lemma(what,whpr).

%Numerals
lex(dt((X^P)^(X^Q)^one(X,and(P,Q))),one):- lemma(one,one).
lex(dt((X^P)^(X^Q)^two(X,and(P,Q))),two):- lemma(two,two).
lex(dt((X^P)^(X^Q)^three(X,and(P,Q))),three):- lemma(three,three).
lex(dt((X^P)^(X^Q)^four(X,and(P,Q))),four):- lemma(four,four).
lex(dt((X^P)^(X^Q)^five(X,and(P,Q))),five):- lemma(five,five).
lex(dt((X^P)^(X^Q)^six(X,and(P,Q))),six):- lemma(six,six).
lex(dt((X^P)^(X^Q)^seven(X,and(P,Q))),seven):- lemma(seven,seven).
lex(dt((X^P)^(X^Q)^eight(X,and(P,Q))),eight):- lemma(eight,eight).
lex(dt((X^P)^(X^Q)^nine(X,and(P,Q))),nine):- lemma(nine,nine).
lex(dt((X^P)^(X^Q)^ten(X,and(P,Q))),ten):- lemma(ten,ten).

%Auxilary_Verb
lex(be,Word) :- lemma(Word,be).
lex(rel,Word):- lemma(Word,rel).
lex(vacp,Word):- lemma(Word,vacp).
lex(there,there).

%Negation
lex(not,not).


%%%%%%%%%% ------------ Lexicons

%%%%%%%%%% ------------ Lexicons with inflections

lex(iv(X^P,[]),Y):-lemma(Word,iv),atom_concat(Word,M,Y),suffix(M),P=.. [Word,X].
lex(iv(X^P,[]),Y):-lemma(Word,iv),atom_concat(Temp,e,Word),sub_atom(Y,_,_,_,Temp),atom_concat(Temp,ing,Y),P=.. [Word,X].

lex(tv(K^W^P,[]),Y):-lemma(Word,tv),atom_concat(Word,M,Y),suffix(M),P=.. [Word,K,W].
lex(tv(K^W^P,[]),Y):-lemma(Word,tv),atom_concat(Temp,e,Word),sub_atom(Y,_,_,_,Temp),atom_concat(Temp,ing,Y),P=.. [Word,K,W].

lex(be,Y):-lemma(Word,be),atom_concat(Word,M,Y),suffix(M).
lex(be,Y):-lemma(Word,be),atom_concat(Temp,e,Word),sub_atom(Y,_,_,_,Temp),atom_concat(Temp,ing,Y).

lex(n(X^P),Y):- lemma(Word,n),atom_concat(Word,s,Y), P =.. [Word,X].
lex(n(X^P),Y):- lemma(Word,n),atom_concat(Word,es,Y), P =.. [Word,X].

%%%%%%%%%% ------------ End Lexicons with inflections


% ...

% --------------------------------------------------------------------
% Suffix types
% --------------------------------------------------------------------
suffix(s).
suffix(es).
suffix(ed).
suffix(d).
suffix(ing).

% ...

% --------------------------------------------------------------------
% Phrasal rules
% rule(+LHS,+ListOfRHS)
% --------------------------------------------------------------------

%%%% -------------------- Rules

rule(np((X^Y)^exists(X,and(Z,Y))),[n(X^Z)]).
rule(np(Y),[dt(X^Y),n(X)]).
rule(np(X),[pn(X)]).

rule(n(A^C),[n(A^B),pp1((A^B)^C)]).
rule(n(A),[adj(B^A),n(B)]).

rule(ppvac(C),[vacp,np(C)]).
rule(vp(X^not(Z),WH),[be,not,vp(X^Z,WH)]).

rule(pp1(C),[p1(A^B^C),np(A^B)]).
rule(pp2(A^B),[p2(A^C),np(C^B)]).

rule(vp(A^B,[]),[tv(A^C,[]),np(C^B)]).
rule(vp(A^B,[]),[tv(A^C,[]),ppvac(C^B)]).
rule(vp(X,WH),[iv(X,WH)]).


rule(ynq(Y),[be, np(X^Y),vp(X,[])]).
rule(s(B,WH),[np(A^B),vp(A,WH)]).
rule(s(X,[WH]),[vp(X,[WH])]).
rule(s(B,[]),[there,ynq(B)]).
rule(ynq(Y),[be, np(X^Y),pp2(X)]).

rule(Y,[whpr(X^Y),vp(X,[])]).
rule(Y,[whpr(X^Y),be,pp2(X)]).

rule(rc(Y,[X]),[rel,s(Y,[X])]).
rule(rc(Y,[]),[rel,vp(Y,[])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(X^Z,[])]).
rule(n(X^and(Y,Z)),[n(X^Y),rc(Z,[X])]).

rule(iv(X^A,[Y]),[tv(X^Y^A,[])]).
rule(tv(Y^A,[X]),[tv(X^Y^A,[])]).

rule(Z,[whpr((X^Y)^Z), inv_s(Y,[X])]).
rule(inv_s(Y,[WH]),[be, np(X^Y),vp(X,[WH])]).
rule(np(X),[there,np(X)]).

rule(vp(K^Z,[]),[dtv(K^W^P^R,[]),np((W^Q)^Z),ppvac((P^R)^Q)]).
rule(vp(K^Z,[]),[dtv(K^W^P^R,[]),np((P^Q)^Z),np((W^R)^Q)]).

rule(ynq(M),[be,there,np((X^Y)^M)]):- Y = exists(R, and(earth(R), in(X, R))).


%%%% ------------------- End of Rules



% ===========================================================
%  Modelchecker:
%  1. If input is a declarative, check if true
%  2. If input is a yes-no question, check if true
%  3. If input is a content question, find answer
% ===========================================================

model([a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,q,r,s,t,u,v,w,x,y,z,
a1,b1,c1,d1,e1,f1,g1,h1,i1,j1,k1,l1,m1,n1,o1,p1,q1,r1,s1,t1,u1,v1,w1,x1,y1,z1,
a2,b2,c2,d2],
[

[put,[[a,f1,h],[a,w1,h],[a,a2,b2]]],
[drink,[[a,v],[a,d2]]],
[drank,[[a,v],[a,d2]]],
[skim,[d2]],
[white,[e,f,b2,v1]],
[eat,[[d1,h1]]],
[ate,[[d1,h1]]],
[yellow,[b,a2]],
[red,[a1,q1]],
[expire,[l]],
[empty,[o,v1]],
[green,[n,o]],
[blue,[f1,g,x1]],
[middle,[i]],
[top,[h]],
[bottom,[m]],


[on,[[e,m],[f,i],[g,h],[x1,h],[b,i],[o,h],[f1,h],[w1,h],[a2,b2]]],
[inside,[ [q1,u],[k1,z1],[n1,y1],[z1,x1],[y1,g],[w,u],[n1,m],[m1,m],[l1,m],[k1,m],[u1,g1],[e1,g1],[p1,u],[o1,u],[r1,u],[q1,u],[s1,u],[t1,u],[c,b],[d,b],[j,e],[p,n],[q,n],[r,f1],[s,u],[t,u],[a1,o],[e1,o],[e1,v1],[v1,g1],[h1,z],[k1,x]]],
[belong,[[v1,d1],[k1,z1],[n1,y1],[z1,x1],[y1,g],[w,u],[n1,m],[m1,m],[l1,m],[k1,m],[u1,g1],[e1,g1],[p1,u],[o1,u],[r1,u],[q1,u],[s1,u],[t1,u],[c,b],[d,b],[j,e],[p,n],[q,n],[r,f1],[s,u],[t,u],[a1,o],[e1,o],[e1,v1],[v1,g1],[h1,z],[k1,x]]],
[in,[ [q1,u],[k1,z1],[n1,y1],[z1,x1],[y1,g],[w,u],[n1,m],[m1,m],[l1,m],[k1,m],[u1,g1],[e1,g1],[p1,u],[o1,u],[r1,u],[q1,u],[s1,u],[t1,u],[c,b],[d,b],[j,e],[p,n],[q,n],[r,f1],[s,u],[t,u],[a1,o],[e1,o],[e1,v1],[v1,g1],[h1,z],[k1,x]]],

[contain,[ [u,q1],[z1,k1],[y1,n1],[x1,z1],[g,y1],[u,w],[m,n1],[m,m1],[m,l1],[m,k1],[g1,u1],[g1,e1],[u,p1],[u,o1],[u,r1],[u,q1],[u,s1],[u,t1],[b,c],[b,d],[f,j],[n,p],[n,q],[f1,r],[u,s],[u,t],[o,a1],[o,e1],[v1,e1],[g1,v1],[z,h1],[x,k1]]],
[has,[ [u,q1],[z1,k1],[y1,n1],[x1,z1],[g,y1],[u,w],[m,n1],[m,m1],[m,l1],[m,k1],[g1,u1],[g1,e1],[u,p1],[u,o1],[u,r1],[u,q1],[u,s1],[u,t1],[b,c],[b,d],[f,j],[n,p],[n,q],[f1,r],[u,s],[u,t],[o,a1],[o,e1],[v1,e1],[g1,v1],[z,h1],[x,k1]]],
[of,[[z1,k1],[y1,n1],[x1,z1],[g,y1],[u,w],[m,n1],[m,m1],[m,l1],[m,k1],[g1,u1],[g1,e1],[u,p1],[u,o1],[u,r1],[u,q1],[u,s1],[u,t1],[b,c],[b,d],[f,j],[n,p],[n,q],[f1,r],[u,s],[u,t],[o,a1],[o,e1],[v1,e1],[g1,v1],[z,h1],[x,k1]]],


[box,[n,o,f1,a1,v1,a2]],
[bowl,[b,b2]],
[egg,[c,d]],
[milk,[l,v,d2]],
[shelf,[h,i,m]],
[container,[e,f,g,x1]],
[banana,[j,k]],
[ham,[p,q,r]],
[watermelon,[s,t]],
[fridge,[u]],
[almond,[v]],
[sandwich,[x,y,z,y1,z1,w]],
[sam,[a]],
[sue,[d1]],
[popsicle,[e1]],
[freezer,[g1]],
[chicken,[h1]],
[sausage,[i1]],
[steak,[j1]],
[tomato,[k1]],
[onion,[l1]],
[carrot,[m1]],
[spinach,[n1]],
[orange,[o1,p1]],
[apple,[q1,r1]],
[mango,[s1,t1]],
[icecream,[u1]]
]).


modelchecker([s(B,[])],Result):- sat([],B,_),valid(Result).
modelchecker([s(B,[])],Result):- \+ sat([],B,_),invalid(Result).
modelchecker([ynq(B)],Result):- sat([],B,_),yq(Result).
modelchecker([ynq(B)],Result):- \+ sat([],B,_),nq(Result).
modelchecker([q(_,B)],Result):- findall((X),(sat([],B,[_|[[_|[G3]]]]),checker(X,G3)),Result).
modelchecker([q(_,B)],Result):- \+ sat([],B,_),dne(Result).

dne([]).
valid([true_in_the_model]).
invalid([not_true_in_the_model]).
yq([yes_to_question]).
nq([no_to_question]).

% ==================================================
% Function i
% Determines the value of a variable/constant in an assignment G
% ==================================================

i(Var,G,Value):-
    var(Var),
    member([Var2,Value],G),
    Var == Var2.

i(C,_,Value):-
   nonvar(C),
   f(C,Value).


% ==================================================
% Function F
% Determines if a value is in the denotation of a Predicate/Relation
% ==================================================

checker(List,Value):-
   model(_,F), findall(Symbol,(member([Symbol,ListOfValues],F),member(Value,ListOfValues)),A),
   atomic_list_concat(A,' ',List).

f(Symbol,Value):-
   model(_,F), member([Symbol,ListOfValues],F),
    member(Value,ListOfValues),!.


f(Symbol,Value):-
   model(_,F), isa(X,Symbol),
    member([X,ListOfValues],F),
    member(Value,ListOfValues).


% ==================================================
% Extension of a variable assignment
% ==================================================

extend(G,X,[ [X,Val] | G]):-
   model(D,_),
   member(Val,D).

% ==================================================
% Always true sat rules
% ==================================================

sat(G1,thing(X),G3):-
   extend(G1,X,G3).

sat(G1,person(X),G3):-
   extend(G1,X,G3).

sat(G,and(earth(_),_),G).

% ==================================================
% Existential quantifier and Numerals
% ==================================================

sat(G1,exists(X,Formula),G3):-
   extend(G1,X,G2),
   sat(G2,Formula,G3).

sat(G1,one(X,Formula),G3):-
   findall((G3),sat(G1,exists(X,Formula),G3),L1),length(L1,N),N>=1,nl.
sat(G1,two(X,Formula),G3):-
   findall((G3),sat(G1,exists(X,Formula),G3),L1),length(L1,N),N>=2,nl.
sat(G1,three(X,Formula),G3):-
   findall((G3),sat(G1,exists(X,Formula),G3),L1),length(L1,N),N>=3,nl.
sat(G1,four(X,Formula),G3):-
   findall((G3),sat(G1,exists(X,Formula),G3),L1),length(L1,N),N>=4,nl.
sat(G1,five(X,Formula),G3):-
   findall((G3),sat(G1,exists(X,Formula),G3),L1),length(L1,N),N>=5,nl.
sat(G1,six(X,Formula),G3):-
   findall((G3),sat(G1,exists(X,Formula),G3),L1),length(L1,N),N>=6,nl.
sat(G1,seven(X,Formula),G3):-
   findall((G3),sat(G1,exists(X,Formula),G3),L1),length(L1,N),N>=7,nl.
sat(G1,eight(X,Formula),G3):-
   findall((G3),sat(G1,exists(X,Formula),G3),L1),length(L1,N),N>=8,nl.
sat(G1,nine(X,Formula),G3):-
   findall((G3),sat(G1,exists(X,Formula),G3),L1),length(L1,N),N>=9,nl.
sat(G1,ten(X,Formula),G3):-
   findall((G3),sat(G1,exists(X,Formula),G3),L1),length(L1,N),N>=10,nl.


% ==================================================
% Definite quantifier (semantic rather than pragmatic account)
% ==================================================

 sat(G1,the(X,and(A,B)),G3):-
   sat(G1,exists(X,and(A,B)),G3),
   i(X,G3,Value),
   \+ ( ( sat(G1,exists(X,A),G2), i(X,G2,Value2), \+(Value = Value2)) ).


% ==================================================
% Negation
% ==================================================

sat(G,not(Formula2),G):-
   \+ sat(G,Formula2,_).


% ==================================================
% Universal quantifier
% ==================================================

sat(G, forall(X,Formula2),G):-
  sat(G,not( exists(X,not(Formula2) ) ),G).


sat(G,no(X,Formula2),G):-
  sat(G,exists(X,not(Formula2)),G).


% ==================================================
% Conjunction
% ==================================================

sat(G1,and(Formula1,Formula2),G3):-
  sat(G1,Formula1,G2),
  sat(G2,Formula2,G3).


% ==================================================
% Disjunction
% ==================================================


sat(G1,or(Formula1,Formula2),G2):-
  ( sat(G1,Formula1,G2) ;
    sat(G1,Formula2,G2) ).


% ==================================================
% Implication
% ==================================================

sat(G1,imp(Formula1,Formula2),G2):-
   sat(G1,or(not(Formula1),Formula2),G2).


% ==================================================
% Predicates
% ==================================================

sat(G,Predicate,G):-
   Predicate =.. [P,Var],
   \+ (P = not),
   i(Var,G,Value),
   f(P,Value).

% ==================================================
% Two-place Relations
% ==================================================

sat(G,Rel,G):-
   Rel =.. [R,Var1,Var2],
   \+ ( member(R,[exists,forall,and,or,imp,the]) ),
   i(Var1,G,Value1),
   i(Var2,G,Value2),
   f(R,[Value1,Value2]).


% ===========================================================
%  Respond
%  For each input type, react appropriately.
% ===========================================================

% Declarative true in the model
respond(Evaluation) :-
		Evaluation = [true_in_the_model],nl,
		write('That is correct'),!.

% Declarative false in the model
respond(Evaluation) :-
		Evaluation = [not_true_in_the_model],nl,
		write('That is not correct'),!.

% Yes-No interrogative true in the model
respond(Evaluation) :-
		Evaluation = [yes_to_question],nl,
		write('yes').

% Yes-No interrogative false in the model
respond(Evaluation) :-
		Evaluation = [no_to_question],nl,
		write('no').

% wh-interrogative true in the model
% ...
respond(Evaluation) :-
		Evaluation \= [],nl, write(Evaluation).

% wh-interrogative false in the model
% ...

respond(Evaluation) :-
		Evaluation = [],nl, write('My knowledge is limited by the programming abilities of my creator.').
