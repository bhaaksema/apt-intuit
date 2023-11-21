% -----------------------------------------------------------------
% g4ip.pl - A sequent calculus prover implemented in Prolog
% -----------------------------------------------------------------

% operator definitions
:- op(1000, xfy, &).    % conjunction
:- op(1100, xfy, '|').  % disjunction
:- op(1110, xfy, =>).   % implication

% -----------------------------------------------------------------
prove0(F) :- prove([] > [F]).
% -----------------------------------------------------------------

% axioms
prove(G > A) :- member(A, G), !.
prove(G > _) :- member(0, G).

% conjunction
prove(G > E) :- select1(A&B, G, G1), !, % lower sequent
                prove([A, B | G1] > E). % upper sequent

prove(G > A&B) :- !, prove(G > A), prove(G > B).

% disjunction
prove(G > E) :- select1(A'|'B, G, G1), !,
                prove([A | G1] > E), prove([B | G1] > E).

prove(G > A'|'B) :- !, prove(G > A); prove(G > B).

% implication (G3ip)
prove(G > E) :- select1(A=>B, G, G1), !,
                prove(G > A), prove([B | G1] > E).

prove(G > A=>B) :- !, prove([A | G] > B).

% -----------------------------------------------------------------
% if X in L, then L1 = L \ {X}
select1(X, L, L1) :- append(L2, [X | L3], L), append(L2, L3, L1).
% -----------------------------------------------------------------
