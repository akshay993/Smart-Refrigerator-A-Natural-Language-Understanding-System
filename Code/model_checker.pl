% Testbed

t(1):- write('sat([],exists(X,and(dog(X),exists(Y,and(cat(Y),chase(X,Y))))),G).'),nl,
         sat([],exists(X,and(dog(X),exists(Y,and(cat(Y),chase(X,Y))))),G),
         nl,
         numbervars(G,0,_),
         write(G).

t(2):- write('sat([],forall(X,and(dog(X),exists(Y,and(cat(Y),chase(X,Y))))),G).'),nl,
         sat([],forall(X,and(dog(X),exists(Y,and(cat(Y),chase(X,Y))))),_).

t(3):- write('sat([],forall(X,imp(dog(X),exists(Y,and(cat(Y),chase(X,Y))))),G).'),nl,
         sat([],forall(X,imp(dog(X),exists(Y,and(cat(Y),chase(X,Y))))),_).

t(4):- sat([],exists(X,imp(person(X),not(exists(Y,and(box(Y),contain(Y,X)))))),G),
        write(G).




% __________________________________________________
%
%             MODEL CHECKER (closed world assumption)
% __________________________________________________



% ==================================================
% A simple model
% ==================================================

model([a,b,c,r],
           [ [cat, [a,b]], [dog,[c]], [die, [c,r,d]], [chase, [ [a,b], [c,a], [c,b] ]] ]).



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

f(Symbol,Value):-
   model(_,F),
    member([Symbol,ListOfValues],F),
    member(Value,ListOfValues).


% ==================================================
% Extension of a variable assignment
% ==================================================

extend(G,X,[ [X,Val] | G]):-
   model(D,_),
   member(Val,D).


% ==================================================
% Existential quantifier
% ==================================================

sat(G1,exists(X,Formula),G3):-
   extend(G1,X,G2),
   sat(G2,Formula,G3).


% ==================================================
% Existential quantifier
% ==================================================

% sat(G1,the(X,Formula),G3):-
%   sat(G1,exists(X,Formula2),G3),
%   findall(G2,  sat(G1,exists(X,Formula2),G2),   L),
%   \+ (select([Y,V],L,LRest), X == Y, member([Y,V],LRest)).


% sat(G1,the(X,Formula),G3):-
%  sat(G1,exists(X,Formula),G3),
%   i(X,G3,Value),
 %  \+ ( ( sat(G1,exists(X,Formula),G2), i(X,G2,Value2), \+(Value = Value2)) ).


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
