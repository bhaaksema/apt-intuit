% g4ip.pl - A sequent calculus prover implemented in Prolog

%% OPERATORS
:- op( 250, fy, ~).     % negation
:- op( 550, xfy, &).    % conjunction
:- op(1025, xfy, '|').  % disjunction
:- op(1050, xfy, =>).   % implication

% Rewrite negation to implication
prove(G > (~E)) :- prove(G > (E=>0)), !.
prove(G > E) :- select1(~A, G, G1), !, prove([A=>0|G1] > E).

% Axiom 1
prove(G > _) :- member(0, G).

% Axiom 2
prove(G > P) :- member(P, G), !.

% left 0 implication (invertible)
prove(G > E) :- select1(P=>B, G, G1), select1(P, G1, G2), !,
    prove([P, B | G2] > E).

% left & implication (invertible)
prove(G > E) :- select1((C&D)=>B, G, G1), !,
    prove([C=>(D=>B) | G1] > E).

% left | implication (invertible)
prove(G > E) :- select1((C'|'D)=>B, G, G1), !,
    prove([C=>B, D=>B | G1] > E).

% left => implication (non-invertible)
prove(G > E) :- select1((C=>D)=>B, G, G1),
    prove([D=>B | G1] > C=>D), prove([B | G1] > E).

% right implication (invertible)
prove(G > (A=>B)) :- !, prove([A | G] > B).

% left conjunction (invertible)
prove(G > E) :- select1(A&B, G, G1), !,
    prove([A, B | G1] > E).

% right conjunction (invertible)
prove(G > (A&B)) :- !, prove(G > A), prove(G > B).

% left disjunction (invertible)
prove(G > E) :- select1(A'|'B, G, G1), !,
    prove([A | G1] > E), prove([B | G1] > E).
              
% right disjuction (non-invertible)
prove(G > (A|B)) :- prove(G > A); prove(G > B).

%% AUXILIARY PREDICATES
select1(X, L, L1) :- append(L2, [X | L3], L), append(L2, L3, L1).

%% PROVER
prove0(F) :- once(prove([] > F)).
