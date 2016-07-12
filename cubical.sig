sig cubical.

%%%% Natural numbers %%%%%%%%%%%%%%%%%%%%%%%%%%%%%
kind nat     type.                                % I, J, K

type z       nat.                                 % 0
type s       nat -> nat.                          % succ(K)

type nat     nat -> o.                            % |- K nat


%%%% Dimensions and dimension lists %%%%%%%%%%%%%%
kind dim     type.                                % R, S, X, Y, Z; x, y, z
kind dlist   type.                                % Rs, Ss, Xs, Ys, Zs

% Dimensions (also by assumption)
type d0      dim.                                 % 0
type d1      dim.                                 % 1

type dim     dim -> o.                            % |- R dim (hyp, check)

% Dimension lists
type d$      dlist.                               % nil
type d+      dim -> dlist -> dlist.               % cons(R, Rs)

type dlist   dlist -> nat -> o.                   % |- Rs dlist_K

% Helper predicates
type is_eps  dim -> o.                            % |- R is_epsilon
type findeps dlist -> nat -> dim -> o.            % |- findeps Rs I E      (+--)
type dlextr  dlist -> nat -> dim -> dlist -> o.   % |- Rs@I = R'+Rs' (++--,-+++)
type dlsnoc  dlist -> dim -> dlist -> o.          % |- Rs ++ [R] = Rs+     (++-)


%%%% Terms and tube lists (mutual) %%%%%%%%%%%%%%%
kind tm      type.                                % A, B, F, L, M, N, P, T; a
kind tlist   type.                                % Ns

% Terms
type pit     tm -> (tm -> tm) -> tm.	          % Pi(A, a.B)
type sigt    tm -> (tm -> tm) -> tm.	          % Sigma(A, a.B)
type idt     (dim -> tm) -> tm -> tm -> tm.       % Id(x.A; P0, P1)
type boolt   tm.				  % bool
type nott    dim -> tm.			          % not_R
type s1t     tm.                                  % S^1

type lam     (tm -> tm) -> tm.		          % \a.M
type app     tm -> tm -> tm.		          % app(M, N)
type pair    tm -> tm -> tm.		          % <M, N>
type fst     tm -> tm.			          % fst(M)
type snd     tm -> tm.			          % snd(M)
type dabs    (dim -> tm) -> tm.		          % <x>M
type dapp    tm -> dim -> tm.		          % M @ r
type tt      tm.				  % true
type ff      tm.				  % false
type if      (tm -> tm) -> tm -> tm -> tm -> tm.  % if_{a.A}(M; T, F)
type notel   dim -> tm -> tm.                     % notel_R(M)
type base    tm.				  % base
type loop    dim -> tm.                           % loop_R
type s1-elim (tm -> tm)                           % S^1-elim_{a.A}
                 -> tm -> tm -> (dim -> tm) -> tm.%    (M; P, x.L)
type coe     (dim -> tm) -> dim -> dim -> tm -> tm.% coe_{y.A}^{R -> R'}(M)
type hcom    tm -> dlist -> dim -> dim            % hcom_{A, Rs}^{R -> R'}
                -> tm -> (dim -> tlist) -> tm.    %    (M, y.Ns)

% Tube lists
type t$      tlist.                               % nil
type t+      tm -> tm -> tlist -> tlist.          % cons(N0, N1; Ns)

% Formation judgments (likewise mutual)
type tm      tm -> o.                             % |- M tm
type tlist   tlist -> nat -> o.                   % |- Ns tlist_K

% Helper predicates
type tubef   tlist -> nat -> dim -> tm -> o.      % |- Ns[I]_E = N        (+++-)
type tlsnoc  tlist -> tm -> tm -> tlist -> o.     % |- Ns ++ (N0,N1) = Ns+(+++-)
type map     (tm -> tm) -> tlist -> tlist -> o.   % |- map[a.M](Ns) = Ns'  (++-)
type let     (dim -> tm) -> (dim -> tm) -> o.     % |- F := M               (-+)
type notdef  (tm -> tm) -> o.                     % |- Not := x\ not(x)      (-)


%%%% Operational semantics %%%%%%%%%%%%%%
type red     tm -> tm -> o.                       % |- M |-> M'
