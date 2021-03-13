(* Dynamic.v- Attempting to nail down some of the dynamic elements of CHS *)

Load Vect.

Definition tud : forall (m : nat) (u : Vect statterm m), HetVect m u -> Set
    :=  fun (m : nat) (u : Vect statterm m) (h : HetVect m u) =>
        {n : nat & {v : Vect statterm n & {h' : HetVect n v | h' isSubHetVectof h}}}.

Definition con : forall n : nat, Vect statterm n -> Set
    :=  fun (n : nat) (v : Vect statterm n) => forall h : HetVect n v, prop * (tud n v h).

Definition kon : forall m : nat, Vect statterm m -> Set
    :=  fun (m : nat) (u : Vect statterm m) => forall (n : nat) (v : Vect statterm n), con n v -> con (m + n) (u ++ v).

(* Given any HetVect h, returns an empty tud stack [hnil_bot is defined in Vect.v] *)
Definition empty_tud : forall {n : nat} {v : Vect statterm n} (h : HetVect n v), tud n v h
    :=  fun (n : nat) (v : Vect statterm n) (h : HetVect n v) =>
        existT  (fun i : nat => {l : Vect statterm i & {h' : HetVect i l | h' isSubHetVectof h}})
                0
                (existT (fun l : Vect statterm 0 => {h' : HetVect 0 l | h' isSubHetVectof h})
                        []
                        (exist (fun h' : HetVect 0 [] => h' isSubHetVectof h) hnil (hnil_bot h))).

(*  For the moment, the returned TUD stack is just that generated from k;
    need to figure out how to combine it with the TUD stack from c *)
(* Types didn't seem to work out in an obvious way *)
Definition cc : forall {m : nat} {u : Vect statterm m}, kon m u -> kon m u
    :=  fun (m : nat) (u : Vect statterm m) (k : kon m u) (n : nat) (v : Vect statterm n) (c : con n v) (h : HetVect (m+n) (u ++ v)) =>
        let (h1,h2) := (hsplit_at h) in
        let (p,t)   := (c h2) in
        let (q,t')  := (k n v c h) in
        (p and q,t').

(* new cc : pair of conjunction of prop args, then append kon tud onto con tud *)
(* define AND as well *)

(* since (h AND k) is usually taken to mean that h precedes k, typing AND s.t. k'r DR's are on top
 [hence the variable flip in the return type] *)
(* Oh yeah- so fun thing about formalizing AND is dealing with some of the associativity issues related to +/++/+++ *)
(* Definition d_AND : forall {m n : nat} {u : Vect statterm m} {v : Vect statterm n}, kon m u -> kon n v -> kon (n+m) (v++u)
    :=  fun (m n : nat) (u : Vect statterm m) (v : Vect statterm n) (h : kon m u) (k : kon n v) (j : nat) (w : Vect statterm j)
            (c : con j w) (hv : HetVect ((n + m) + j) ((v ++ u) ++ w)) =>
        let (a,r) := (hsplit_at hv) in
        let (l1,l2) := (hsplit_at a) in
        let (p,t) := (h j w c (l2 +++ r)) in
        let (q,t0) := (k (m + j) (u ++ w) (cc h j w c) (l1 +++ (l2 +++ r))) in
        (p and q, ?FOO).
        ?FOO : tud ((n+m)+j) ((v ++ u) ++ w) hv *)
        (* can't figure this out exactly right now… *)



(* NOT only applies assertions, not questions *)
(* ie kon's with empty tud *)
(* future work though- just model off Carl and Scott's paper *)
(* Decided to make the return tud be empty- we can always change that behavior later if we want to *)
Definition NOT : forall {m : nat} {u : Vect statterm m}, kon m u -> kon 0 []
    :=  fun (m : nat) (u : Vect statterm m) (k : kon m u) (n : nat) (v : Vect statterm n) (c : con n v) (h : HetVect n v) =>
        (not (hexists (fun h' : HetVect m u => fst (k n v c (h' +++ h)))),empty_tud h).
