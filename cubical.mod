module cubical.

%%%% Natural numbers %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Formation judgment for (closed) natural numbers: |- K nat
nat z.
nat (s K) :- nat K.



%%%% Dimensions and dimension lists %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Formation judgment for dimensions: |- R dim (variable cases assumed)
dim d0.
dim d1.


% Formation judgment for dimension lists of length K: |- Rs dimlist_K 
dlist d$ z.
dlist (d+ R Rs) (s K) :- dim R, dlist Rs K.


% Dimension constants
is_eps d0.
is_eps d1.


% Find a dimension constant in Rs and return its position and value
findeps (d+ E Rs) z E :- is_eps E.
findeps (d+ R Rs) (s I) E :- findeps Rs I E.


% Result of extracting Ith element of a (non-nil) dimension list
% (counting from 0): |- Rs[[I]] = R' + Rs'
dlextr (d+ R Rs) z R Rs.
dlextr (d+ R Rs) (s I) R' (d+ R Rs') :- dlextr Rs I R' Rs'.


% Result of adding a dimension to the end of a dlist: |- Rs ++ [R] = Rs+
dlsnoc d$ R (d+ R d$).
dlsnoc (d+ R' Rs) R (d+ R' Rs+) :- dlsnoc Rs R Rs+.



%%%% Terms and tube lists %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Formation judgment for terms: |- M tm.
tm (pit A B) :- tm A, pi a\ tm a => tm (B a).
tm (sigt A B) :- tm A, pi a\ tm a => tm (B a).
tm (idt A M N) :- pi x\ dim x => tm (A x), tm M, tm N.
tm boolt.
tm (nott R) :- dim R.
tm s1t.
tm (lam M) :- pi a\ tm a => tm (M a).
tm (app M N) :- tm M, tm N.
tm (pair M N) :- tm M, tm N.
tm (fst M) :- tm M.
tm (snd M) :- tm M.
tm (dabs M) :- pi x\ dim x => tm (M x).
tm (dapp M R) :- tm M, dim R.
tm tt.
tm ff.
tm (if A M N1 N2) :- pi a\ tm a => tm (A a), tm M, tm N1, tm N2.
tm (notel R M) :- dim R, tm M.
tm base.
tm (loop R) :- dim R.
tm (s1-elim A M N1 N2) :-
  pi a\ tm a => tm (A a),
  tm M,
  tm N1,
  pi x\ dim x => tm (N2 x).
tm (coe A R R' M) :-
  pi y\ dim y => tm (A y),
  dim R,
  dim R',
  tm M.
tm (hcom A Rs R R' M Ns) :-
  tm A,
  dlist Rs (s K),
  dim R,
  dim R',
  tm M,
  pi y\ dim y => tlist (Ns y) (s K).


% Formation judgment for tube lists of length K: |- Ns tlist_K
tlist t$ z.
tlist (t+ T0 T1 Ns) (s K) :- tm T0, tm T1, tlist Ns K.


% E-face of the Ith tube of a (non-nil) tube list (from 0): |- Ns_I^E = T
tubef (t+ N0 N1 Ns) z d0 N0.
tubef (t+ N0 N1 Ns) z d1 N1.
tubef (t+ N0 N1 Ns) (s I) E N :- tubef Ns I E N.


% Add a tube to the end of a tube list: |- Ns ++ [(N0, N1)] = Ns+
tlsnoc t$ N0 N1 (t+ N0 N1 t$).
tlsnoc (t+ N0' N1' Ns) N0 N1 (t+ N0' N1' Ns+) :- tlsnoc Ns N0 N1 Ns+.


% Mapping a term operator across a tlist: |- map[a.M](Ns) = Ns'
map M t$ t$.
map M (t+ N0 N1 Ns) (t+ (M N0) (M N1) Ns') :- map M Ns Ns'.


% Let definition
let M M.


% Not definition
notdef (x\ if (z\ boolt) x ff tt).



%%%% Operational semantics %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Types

red (nott E) boolt :-
  is_eps E.


% Coe and Hcom 

red (coe A R R' M) (coe A' R R' M) :-
  pi y\ red (A y) (A' y).

red (hcom A Rs R R' M Ns) (hcom A' Rs R R' M Ns) :-
  red A A'.


% Pi types

red (app M N) (app M' N) :-
  red M M'.

red (app (lam M) N) (M N).

red (coe (y\ pit (A y) (B y)) R R' M)
    (lam a\ coe (y\ B y (coe A R' y a)) R R' (app M (coe A R' R a))).

red (hcom (pit A B) Rs R R' M Ns)
    (lam a\ hcom (B a) Rs R R' (app M a) (Ns' a)) :-
  pi a\ pi y\ map (t\ app t a) (Ns y) (Ns' a y).


% Sigma types

red (fst M) (fst M') :-
  red M M'.

red (snd M) (snd M') :-
  red M M'.

red (fst (pair M N)) M.

red (snd (pair M N)) N.

red (coe (y\ sigt (A y) (B y)) R R' M)
    (pair (C R') (coe (y\ B y (C y)) R R' (snd M))) :-
  let C (z\ coe A R z (fst M)).

red (hcom (sigt A B) Rs R R' M Ns)
    (pair (H R')
          (hcom (B (H R')) Rs R R' (coe (y\ B (H y)) R R' (snd M)) Ns2)) :-
  pi y\ map fst (Ns y) (Ns1 y),
  let H (z\ hcom A Rs R z (fst M) Ns1),
  pi y\ map (t\ coe (y\ B (H y)) y R' (snd t)) (Ns y) (Ns2 y).


% Identification types

red (dapp M R) (dapp M' R) :-
  red M M'.

red (dapp (dabs M) R) (M R).

red (coe (y\ idt (A y) (P0 y) (P1 y)) R R' M)
    (dabs x\ hcom (A R' x) (d+ x d$) R R'
        (coe (y\ A y x) R R' (dapp M x))
        (y\ t+ (coe (y\ A y x) y R' (P0 y)) (coe (y\ A y x) y R' (P1 y)) t$)).

red (hcom (idt A P0 P1) Rs R R' M Ns)
    (dabs x\ hcom (A x) (Rs+ x) R R' (dapp M x) (y\ Ns+ y x)) :-
  pi x\ dlsnoc Rs x (Rs+ x),
  pi y\ pi x\ map (t\ dapp t x) (Ns y) (Ns' y x),
  pi y\ pi x\ tlsnoc (Ns' y x) P0 P1 (Ns+ y x).


% Bool

red (if A M T F) (if A M' T F) :-
  red M M'.

red (if A tt T F) T.

red (if A ff T F) F.

red (if A (hcom boolt Rs R R' M Ns) T F)
    (hcom (A (H R')) Rs R R' (coe (y\ A (H y)) R R' (if A M T F)) Ns') :-
  let H (z\ hcom boolt Rs R z M Ns),
  pi y\ map (t\ coe (y\ A (H y)) y R' (if A t T F)) (Ns y) (Ns' y).

red (coe (y\ boolt) R R' M) M.

red (hcom boolt Rs R R' M Ns) (Nie R') :-
  findeps Rs I E,
  pi y\ tubef (Ns y) I E (Nie y).

red (hcom boolt Rs R R M Ns) M.


% S1

red (loop E) base :- is_eps E.

red (s1-elim A M P L) (s1-elim A M' P L) :-
  red M M'.

red (s1-elim A base P L) P.

red (s1-elim A (loop R) P L) (L R).

red (s1-elim A (hcom s1t Rs R R' M Ns) P L)
    (hcom (A (H R')) Rs R R' M Ns') :-
  let H (z\ hcom s1t Rs R z M Ns),
  pi y\ map (t\ coe (y\ A (H y)) y R' (s1-elim A t P L)) (Ns y) (Ns' y).

red (coe (y\ s1t) R R' M) M.

red (hcom s1t Rs R R' M Ns) (Nie R') :-
  findeps Rs I E,
  pi y\ tubef (Ns y) I E (Nie y).

red (hcom s1t Rs R R M Ns) M.


% not_x

red (notel d0 M) (Not M) :- notdef Not.
red (notel d1 M) M.

red (coe nott R R' M) (coe nott R R' M') :-
  red M M'.

red (coe nott d0 R' M) (notel R' (Not M)) :- notdef Not.
red (coe nott d1 R' M) (notel R' M).

red (coe nott R R' (notel R M)) (notel R' M).

red (coe (y\nott X) R R' M) M.

red (hcom (nott W) Rs R R' M Ns)
    (notel W (hcom boolt Rs R R' (coe nott W d1 M) Ns')) :-
  pi y\ map (t\ coe nott W d1 t) (Ns y) (Ns' y).
