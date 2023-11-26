% g4ip.pl - A sequent calculus prover implemented in Prolog

% Operator definitions (TPTP syntax)
:- op(1000, xfy, &).    % conjunction
:- op(1100, xfy, '|').  % disjunction
:- op(1110, xfy, =>).   % implication

% Invertible sequent calculus rules
prove(G > P) :- member(P, G), !.                             % initial sequent
prove(G > _) :- member(0, G).                                % (⊥ =>)
prove(G > (A&B)) :- !, prove(G > A), prove(G > B).           % (=> &)
prove(G > E) :- select1(A&B, G, G1), !,                      % (& =>)
    prove([A, B | G1] > E).
prove(G > E) :- select1(A'|'B, G, G1), !,                    % (| =>)
    prove([A | G1] > E), prove([B | G1] > E).
prove(G > (A=>B)) :- !, prove([A | G] > B).                  % (=> ->)
prove(G > E) :- select1(P=>B, G, G1), select1(P, G1, G2), !, % (P-> =>)
    prove([P, B | G2] > E).
prove(G > E) :- select1((C&D)=>B, G, G1), !,                 % (&-> =>)
    prove([C=>(D=>B) | G1] > E).
prove(G > E) :- select1((C'|'D)=>B, G, G1), !,               % (|-> =>)
    prove([C=>B, D=>B | G1] > E).

% Non-invertible sequent calculus rules
prove(G > (A|B)) :- prove(G > A); prove(G > B).              % (=> |)
prove(G > E) :- select1((C=>D)=>B, G, G1),                   % (->-> =>)
    prove([D=>B | G1] > C=>D), prove([B | G1] > E).

% Selection predicate (L = L1 + {X})
select1(X, L, L1) :- append(L2, [X | L3], L), append(L2, L3, L1).

% Prover entry point
prove0(F) :- once(prove([] > F)).
