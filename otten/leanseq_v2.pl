% -----------------------------------------------------------------
% leanseq.pl - A sequent calculus prover implemented in Prolog
% -----------------------------------------------------------------

% operator definitions (TPTP syntax)

:- op( 500, fy, ~).     % negation
:- op(1000, xfy, &).    % conjunction
:- op(1100, xfy, '|').  % disjunction
:- op(1110, xfy, =>).   % implication
:- op( 500, fy, !).     % universal quantifier:  ![X]:
:- op( 500, fy, ?).     % existential quantifier:  ?[X]:
:- op( 500,xfy, :).

% -----------------------------------------------------------------
prove0(F) :- prove([] > [F]).
% -----------------------------------------------------------------

% axiom
prove(G > D) :- member(A,G), member(A,D), !.

% conjunction
prove(G > D) :- select1(A&B,G,G1), !,
                prove([A,B|G1] > D).

prove(G > D) :- select1(A&B,D,D1), !,
                prove(G > [A|D1]), prove(G > [B|D1]).

% disjunction
prove(G > D) :- select1(A|B,G,G1), !,
                prove([A|G1] > D), prove([B|G1] > D).

prove(G > D) :- select1(A|B,D,D1), !,
                prove(G > [A,B|D1]).

% implication
prove(G > D) :- select1(A=>B,G,G1), !,
                prove(G1 > [A|D]), prove([B|G1] > D).

prove(G > D) :- select1(A=>B,D,D1), !,
                prove([A|G] > [B|D1]).

% negation
prove(G > D) :- select1(~A,G,G1), !,
                prove(G1 > [A|D]).

prove(G > D) :- select1(~A,D,D1), !,
                prove([A|G] > D1).

% -----------------------------------------------------------------
select1(X,L,L1) :- append(L2,[X|L3],L), append(L2,L3,L1).
% -----------------------------------------------------------------
