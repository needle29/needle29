(* 3/13/21- this one is a super early attempt at CDS *)

(* an obvious pointer that I gotta reformulate my def for dy, since stuff like this was meant to be avoided *)
(* n:nat⊢(fun i : nat => eq_rec (max i n) (fun x : nat => kon (S x) 0) (BEAT i n) (max n i) (max_comm i n)) : dy (S n) 1 0 *)

(* Trying DyCG with contents taking two arguments- one for # of pre-existing DR's needed, one for # of DR's introduced *)

Load "CDS_prims".
Load "Vect".
Load "extensions".

(* Some number proofs *)
    (* gonna make them all Fixpoints rather than using nat_ind so they reduce better *)
    Fixpoint Sdistr (m j : nat) {struct m} : (S (m+j)) = (m+(S j))
        := match m as k return ((S (k+j)) = (k+(S j))) with 0 => eq_refl | S i => f_equal S (Sdistr i j) end.

    Fixpoint max_plus (m n : nat) {struct m} : (max m (m+n)) = (m+n)
        := match m as k return ((max k (k+n)) = (k+n)) with 0 => eq_refl | S i => f_equal S (max_plus i n) end.

    Fixpoint max_plus_2 (m n : nat) {struct m} : (max m (S (m+n))) = (S (m+n))
        := match m as k return ((max k (S (k+n))) = (S (k+n))) with 0 => eq_refl | S i => f_equal S (max_plus_2 i n) end.

    Fixpoint Zria (n : nat) {struct n} : n = (n+0)
        := match n as k return (k = (k+0)) with 0 => eq_refl | S i => f_equal S (Zria i) end.

    Fixpoint max_plus_2_in (m n : nat) {struct m} : (S (m+n)) = (max m (S (m+n)))
        := match m as k return ((S (k+n)) = (max k (S (k+n)))) with 0 => eq_refl | S i => f_equal S (max_plus_2_in i n) end.

    Fixpoint add_comm (m n : nat) {struct m} : (m+n) = (n+m)
        := match m as k return ((k+n) = (n+k)) with 0 => Zria n | S i => eq_trans (f_equal S (add_comm i n)) (Sdistr n i) end.

    (* Definition assoc_flip : forall m n k : nat, (m+(n+k)) = (n+(m+k))
        :=  fun m n k : nat =>
            eq_trans' (add_assoc m n k) (eq_trans (f_equal (fun i : nat => i+k) (add_comm m n)) (add_assoc n m k)). *)
    Fixpoint assoc_flip (m n k : nat) {struct m} : (m+(n+k)) = (n+(m+k))
        :=  match m as i return ((i+(n+k)) = (n+(i+k))) with
                | 0     => eq_refl
                | S i   => eq_trans (f_equal S (assoc_flip i n k)) (Sdistr n (i+k))
            end.

(* Proofs used in other proofs/definitions (which are not defined elsewhere): *)
    Definition andb_trans : forall b c d : bool, (b && (c && d)) = ((b && c) && d)
        := fun b c d : bool => bool_ind (fun s : bool => (s && (c && d)) = ((s && c) && d)) eq_refl eq_refl b.

    Definition refl_l_id_trans : forall {A : Type} {x y : A} (e : x = y), e = (eq_trans eq_refl e)
        := fun (A : Type) (x : A) => eq_ind_dep x (fun (z : A) (d : x = z) => d = eq_trans eq_refl d) eq_refl.

    Fixpoint max_idem (m : nat) {struct m} : (max m m) = m
        := match m as k return ((max k k) = k) with 0 => eq_refl | S i => f_equal S (max_idem i) end.

    Fixpoint max_assoc (x y z : nat) {struct x} : (max (max x y) z) = (max x (max y z))
        :=  match x as p,y as q,z as r return ((max (max p q) r) = (max p (max q r))) with
                |   0,  q,  r   =>  @eq_refl nat (max q r)
                | S i,  0,  r   =>  @eq_refl nat (max (S i) r)
                | S i,S j,  0   =>  @eq_refl nat (S (max i j))
                | S i,S j,S k   =>  @f_equal nat nat S (max (max i j) k) (max i (max j k)) (max_assoc i j k)
            end.

    Fixpoint max_comm (m n : nat) {struct m} : (max m n) = (max n m)
        :=  match m as x,n as y return ((max x y) = (max y x)) with
                |   0,  0   =>  eq_refl
                | S i,  0   =>  eq_refl
                |   0,S j   =>  eq_refl
                | S i,S j   =>  f_equal S (max_comm i j)
            end.

    (* Definition max_idemish : forall m n : nat, (max (max m n) n) = (max m n)
        := fun m n : nat => eq_trans (max_trans m n n) (f_equal (max m) (max_idem n)). *)

    Definition max_idemish : forall m n : nat, (max m (max n m)) = (max n m)
        :=  fun m n : nat =>
            eq_trans    (f_equal (max m) (max_comm n m))
                        (eq_trans'  (max_assoc m m n)
                                    (eq_trans (f_equal (fun x : nat => max x n) (max_idem m)) (max_comm m n))).

    Definition max_dist : forall m n k : nat, (max (max m k) (max n k)) = (max (max m n) k)
        :=  fun m n k : nat =>
            eq_trans    (f_equal    (max (max m k)) (max_comm n k))
                        (eq_trans   (max_assoc  m k (max k n))
                                    (eq_trans   (f_equal    (max m)
                                                            (eq_trans   (eq_trans'  (max_assoc k k n)
                                                                                    (f_equal (fun x : nat => max x n) (max_idem k)))
                                                                        (max_comm k n)))
                                                (eq_sym (max_assoc m n k)))).

(* Defining the generalized quantifiers *)
Definition every : forall s : statterm, (Sns s -> prop) -> (Sns s -> prop) -> prop
    := fun (s : statterm) (P Q : Sns s -> prop) => p_forall s (fun x : Sns s => (P x) implies (Q x)).
Definition a     : forall s : statterm, (Sns s -> prop) -> (Sns s -> prop) -> prop
    := fun (s : statterm) (P Q : Sns s -> prop) => p_exists s (fun x : Sns s => (P x) and (Q x)).

Notation "'e^' n" := (Vect e n) (at level 0) : vect_scope.
    (* [] : e^0 *)
    (* (::) : forall {n : nat}, e -> e^n -> e^(S n) *)
    (* head : forall {n : nat}, e^(S n) -> e *)
    (* tail : forall {n : nat}, e^(S n) -> e^n *)
    (* (++) : forall {m n : nat}, e^m -> e^n -> e^(m+n) *)
    (* vsplit_at : forall m n : nat, e^(m+n) -> (e^m)*(e^n) *)
    (* take : forall (m : nat) {n : nat}, e^(m+n) -> e^m *)
    (* drop : forall (m : nat) {n : nat}, e^(m+n) -> e^n *)

(* contexts are the same as before- ∀n:nat, (con n) is a function from an n-length vector of entities to a proposition *)
Definition con : nat -> Set := fun n : nat => e^n -> prop.

(* General quantifiers over e-vectors of any length *)
Fixpoint vexists {n : nat} : con n -> prop
    :=  match n as k return (con k -> prop) with
            | 0     =>  fun c : con 0 => c []
            | S i   =>  fun c : con (S i) => p_exists ent (fun x : e => vexists (fun v : e^i => c (x::v)))
        end.
Fixpoint vforall {n : nat} : con n -> prop
    :=  match n as k return (con k -> prop) with
            | 0     =>  fun c : con 0 => c []
            | S i   =>  fun c : con (S i) => p_forall ent (fun x : e => vforall (fun v : e^i => c (x::v)))
        end.

(* contents now take two arguments- ∀i,m:nat, (kon i m) takes a context with at least i DR's and adds m DR's to it *)
Definition kon : nat -> nat -> Set := fun m i : nat => forall n : nat, con (m+n) -> con (i+(m+n)).

Definition cc : forall m i : nat, kon m i -> kon m i
    :=  fun (m i : nat) (k : kon m i) (n : nat) (c : con (m+n)) (v : e^(i+(m+n))) => (c (drop i v)) and (k n c v).

(* castings for contexts & contents with length arguments implicit (vcast moved to Vect.v) *)
Definition ccast : forall {m : nat}, con m -> forall {n : nat}, m = n -> con n
    :=  fun m : nat => eq_rec m con.
Definition kcast : forall {m i : nat}, kon m i -> forall (j : nat) {n : nat}, (m+j) = n -> con n -> con (i+n)
    := fun (m i : nat) (h : kon m i) (j : nat) => eq_rec (m+j) (fun n : nat => con n -> con (i+n)) (h j).

(* First definition where extra i arg to kon matters- NOT prevents adding NEW DR's, not reference to pre-existing DR's *)
Definition NOT : forall {m i : nat}, kon m i -> kon m 0
    := fun (m i : nat) (k : kon m i) (n : nat) (c : con (m+n)) (v : e^(m+n)) => not (vexists (fun u : e^i => k n c (u++v))).

Definition dynNOT : forall (m i n : nat) (k : kon m i) (c : con (m+n)) (v : e^(m+n)),
    (NOT (NOT k) n c v) ≡ (vexists (fun u : e^i => k n c (u++v)))
    :=  fun (m i n : nat) (k : kon m i) (c : con (m+n)) (v : e^(m+n)) =>
        let q := (vexists (fun u : e^i => k n c (u++v))) in
        conj    (dne q)
                (fun (w : world) (p : (q@w) = true) =>
                 eq_trans (p_not_ax (not q) w) (f_equal negb (eq_trans (p_not_ax q w) (f_equal negb p)))).

(* starting to look a little better I suppose *)
Definition d_AND : forall {m n i j : nat}, kon m i -> kon n j -> kon (max m n) (j+i)
    :=  fun (m n i j : nat) (h : kon m i) (k : kon n j) (a : nat) (c : con ((max m n)+a)) (v : e^((j+i)+((max m n)+a))) =>
        let (x,p)   := (m_frnt m n a) in
        let (y,q)   := (n_frnt m n a) in
        let d       := (ccast c p) in
        let u       := (vcast v (eq_trans (f_equal (plus (j+i)) p) (add_assoc j i (m+x)))) in
        (h x d (drop j u))
        and (kcast k (i+y) (eq_trans (assoc_flip n i y) (f_equal (plus i) (eq_trans' q p))) (cc m i h x d) u).

Infix "AND" := d_AND (at level 0) : dyn_scope.
Open Scope dyn_scope.
(* *so* much better than what it used to look like *)
Definition dynAND : forall (m n i j a : nat) (h : kon m i) (k : kon n j) (c : con ((max m n)+a)) (v : e^((j+i)+((max m n)+a))),
    (cc (max m n) (j+i) (h AND k) a c v)
    ≡
    (let (x,p) := (m_frnt m n a) in
     let (y,q) := (n_frnt m n a) in
     kcast (cc n j k) (i+y) (eq_trans (assoc_flip n i y) (f_equal (plus i) (eq_trans' q p)))
                            (cc m i h x (ccast c p)) (vcast v (eq_trans (f_equal (plus (j+i)) p) (add_assoc j i (m+x)))))
    :=  fun (m n i j a : nat) (h : kon m i) (k : kon n j) (c : con ((max m n)+a)) (v : e^((j+i)+((max m n)+a))) =>
        match (m_frnt m n a) as s, (n_frnt m n a) as t
        return  (((c (drop (j+i) v))
                    and (let (x',p') := s in let (y',q') := t in
                         (h x' (ccast c p') (drop j (vcast v (eq_trans (f_equal (plus (j+i)) p') (add_assoc j i (m+x'))))))
                         and (kcast k (i+y')    (eq_trans (assoc_flip n i y') (f_equal (plus i) (eq_trans' q' p')))
                                                (cc m i h x' (ccast c p'))
                                                (vcast v (eq_trans (f_equal (plus (j+i)) p') (add_assoc j i (m+x')))))))
                 ≡
                 (let (x,p) := s in
                  let (y,q) := t in
                  kcast (cc n j k) (i+y) (eq_trans (assoc_flip n i y) (f_equal (plus i) (eq_trans' q p)))
                        (cc m i h x (ccast c p)) (vcast v (eq_trans (f_equal (plus (j+i)) p) (add_assoc j i (m+x))))))
        with
            | exist _ x p,exist _ y q =>
                let C := (cc m i h x (ccast c p)) in
                let D := (eq_trans (f_equal (plus (j+i)) p) (add_assoc j i (m+x))) in
                let E := (eq_trans (assoc_flip n i y) (f_equal (plus i) (eq_trans' q p))) in
                let u := (vcast v D) in
                proj1 (int_eq
                        ((c (drop (j+i) v)) and ((h x (ccast c p) (drop j u)) and (kcast k (i+y) E C u)))
                        (kcast (cc n j k) (i+y) E C u))
                        (fun w : world =>
                             eq_trans   (p_and_ax (c (drop (j+i) v)) ((h x (ccast c p) (drop j u)) and (kcast k (i+y) E C u)) w)
                            (eq_trans   (f_equal    (andb ((c (drop (j+i) v))@w))
                                                    (p_and_ax (h x (ccast c p) (drop j u)) (kcast k (i+y) E C u) w))
                            (eq_trans   (andb_trans ((c (drop (j+i) v))@w) ((h x (ccast c p) (drop j u))@w)
                                                    ((kcast k (i+y) E C u)@w))
                            (eq_trans   (f_equal    (fun t : bool => t && ((kcast k (i+y) E C u)@w))
                                            (eq_trans
                                                (f_equal (fun b : bool => b && ((h x (ccast c p) (drop j u))@w))
                                                    (let z := ((max m n)+a) in
                                                     eq_ind_dep z
                                                        (fun (r : nat) (d : z = r) =>
                                                            ((c (drop (j+i) v))@w)
                                                            = ((ccast c d
                                                                (drop i (drop j (vcast v
                                                                    (eq_trans (f_equal (plus (j+i)) d) (add_assoc j i r))))))@w))
                                                        (eq_trans
                                                            (f_equal    (fun l : e^z => (c l)@w) (drop_assoc j i z v))
                                                            (f_equal    (fun d : ((j+i)+z) = (j+(i+z)) =>
                                                                            (c (drop i (drop j (vcast v d))))@w)
                                                                        (refl_l_id_trans (add_assoc j i z))))
                                                        (m+x) p))
                                                (eq_sym (p_and_ax   (ccast c p (drop i (drop j u)))
                                                                    (h x (ccast c p) (drop j u)) w))))
                                        (eq_ind_dep (n+(i+y))
                                            (fun (z : nat) (r : n+(i+y) = z) => forall (d : con z) (l : e^(j+z)),
                                                    ((d (drop j l))@w) && ((kcast k (i+y) r d l)@w)
                                                        = ((kcast (cc n j k) (i+y) r d l)@w))
                                            (fun (d : con (n+(i+y))) (l : e^(j+(n+(i+y)))) =>
                                                eq_sym (p_and_ax (d (drop j l)) (k (i+y) d l) w))
                                           (i+(m+x)) E C u)))))
        end.

(* holy f-in' crap. This is beyond ridiculous *)
(* Definition dynAND:forall (m n i j a : nat) (h : kon m i) (k : kon n j) (c : con ((max n m)+a)) (v : e^((j+i)+((max n m)+a))),
    (cc (max n m) (j+i) (h AND k) a c v)
    ≡
    (cc n j k (i+(proj1_sig (m_frnt n m a)))
        (ccast      (cc m i h (proj1_sig (n_frnt n m a)) (ccast c (proj2_sig (n_frnt n m a))))
                    (eq_trans   (f_equal (plus i) (eq_trans' (proj2_sig (n_frnt n m a)) (proj2_sig (m_frnt n m a))))
                                (assoc_flip i n (proj1_sig (m_frnt n m a)))))
        (vcast v    (eq_trans   (f_equal    (plus (j+i)) (proj2_sig (m_frnt n m a)))
                                (eq_trans   (add_assoc j i (n+(proj1_sig (m_frnt n m a))))
                                            (f_equal (plus j) (assoc_flip i n (proj1_sig (m_frnt n m a))))))))
    :=  fun (m n i j a : nat) (h : kon m i) (k : kon n j) (c : con ((max n m)+a)) (v : e^((j+i)+((max n m)+a))) =>
        let b := ((max n m)+a) in
        int_eq  (cc (max n m) (j+i) (h AND k) a c v)
                (cc n j k (i+(proj1_sig (m_frnt n m a)))
                    (ccast      (cc m i h (proj1_sig (n_frnt n m a)) (ccast c (proj2_sig (n_frnt n m a))))
                                (eq_trans   (f_equal (plus i) (eq_trans' (proj2_sig (n_frnt n m a)) (proj2_sig (m_frnt n m a))))
                                            (assoc_flip i n (proj1_sig (m_frnt n m a)))))
                    (vcast v    (eq_trans (f_equal (plus (j+i)) (proj2_sig (m_frnt n m a)))
                                          (eq_trans (add_assoc j i (n+(proj1_sig (m_frnt n m a))))
                                                    (f_equal (plus j) (assoc_flip i n (proj1_sig (m_frnt n m a))))))))
            (fun w : world =>
             match (n_frnt n m a) as s,(m_frnt n m a) as t
             return ((((c (drop (j+i) v))
                        and ((h (proj1_sig s) (ccast c (proj2_sig s))
                               ((drop j (take (j+i) v)) ++ (vcast (drop (j+i) v) (proj2_sig s))))
                             and (k (i+(proj1_sig t))
                                    (ccast      (cc m i h (proj1_sig s) (ccast c (proj2_sig s)))
                                                (eq_trans   (f_equal (plus i) (eq_trans' (proj2_sig s) (proj2_sig t)))
                                                            (assoc_flip i n (proj1_sig t))))
                                    (vcast  v   (eq_trans (f_equal (plus (j+i)) (proj2_sig t))
                                                          (eq_trans (add_assoc j i (n+(proj1_sig t)))
                                                                    (f_equal (plus j) (assoc_flip i n (proj1_sig t)))))))))@w)
                    =
                    (((ccast    (cc m i h (proj1_sig s) (ccast c (proj2_sig s)))
                                (eq_trans   (f_equal (plus i) (eq_trans' (proj2_sig s) (proj2_sig t)))
                                            (assoc_flip i n (proj1_sig t)))
                                (drop j (vcast  v
                                                (eq_trans   (f_equal (plus (j+i)) (proj2_sig t))
                                                            (eq_trans (add_assoc j i (n+(proj1_sig t)))
                                                                      (f_equal (plus j) (assoc_flip i n (proj1_sig t))))))))
                        and (k  (i+(proj1_sig t))   (ccast  (cc m i h (proj1_sig s) (ccast c (proj2_sig s)))
                                                            (eq_trans (f_equal (plus i) (eq_trans' (proj2_sig s) (proj2_sig t)))
                                                                      (assoc_flip i n (proj1_sig t))))
                                                    (eq_rec ((j+i)+b) (Vect e) v (j+(n+(i+(proj1_sig t))))
                                                            (eq_trans (f_equal (plus (j + i)) (proj2_sig t))
                                                                      (eq_trans (add_assoc j i (n+(proj1_sig t)))
                                                                                (f_equal (plus j)
                                                                                    (assoc_flip i n (proj1_sig t))))))))@w))
             with exist _ x p,exist _ y q =>
             let l := (take j (take (j+i) v)) in
             let r := (drop j (take (j+i) v)) in
             let u := (drop (j+i) v) in
             let d := (eq_trans (f_equal (plus i) (eq_trans' p q)) (assoc_flip i n y)) in
             let t := (eq_trans (f_equal (plus (j+i)) q) (eq_trans (add_assoc j i (n+y)) (f_equal (plus j) (assoc_flip i n y)))) in
             let G := (fun (R : nat -> Set) (X : R b) => eq_rec b R X (m+x) p) in
             let U := (G (Vect e) u) in
             let C := (G con c) in
             let R := (k (i+y) (eq_rec (i+(m+x)) con (cc m i h x C) (n+(i+y)) d) (eq_rec ((j+i)+b) (Vect e) v (j+(n+(i+y))) t)) in
             let T := (eq_rec (i+(m+x)) con (cc m i h x C) (n+(i+y)) d (drop j (eq_rec ((j+i)+b) (Vect e) v (j+(n+(i+y))) t))) in
             (eq_trans  (p_and_ax (c u) ((h x C (r ++ U)) and R) w)
             (eq_trans  (f_equal (andb ((c u)@w)) (p_and_ax (h x C (r ++ U)) R w))
             (eq_trans  (andb_trans ((c u)@w) ((h x C (r ++ U))@w) (R@w))
             (eq_trans
                (f_equal (fun s : bool => s && (R@w))
                    (eq_trans
                        (f_equal  (fun s : bool => s && ((h x C (r ++ U))@w))
                            (eq_trans   (eq_ind_dep b (fun (z : nat) (s : b = z) =>
                                                        ((c u)@w) = ((eq_rec b con c z s (eq_rec b (Vect e) u z s))@w))
                                                    eq_refl (m+x) p)
                                        (f_equal (fun xs : e^(m+x) => (C xs)@w) (tkdr_app_inv2b i r U))))
                        (eq_trans'
                            (p_and_ax (C (drop i (r ++ U))) (h x C (r ++ U)) w)
                            (eq_ind_dep (i+(n+y))
                                (fun (z : nat) (A : (i+(n+y)) = z) =>
                                   ((cc m i h x C (r ++ U))@w) =
                                   ((eq_rec (i+(m+x)) con (cc m i h x C) z (eq_trans (f_equal (plus i) (eq_trans' p q)) A)
                                        (drop j (eq_rec ((j+i)+b) (Vect e) v (j+z)
                                                        (eq_trans (f_equal (plus (j+i)) q)
                                                                  (eq_trans (add_assoc j i (n+y)) (f_equal (plus j) A))))))@w))
                                (eq_ind_dep b
                                    (fun (z : nat) (s : b = z) => forall E : con (i+z),
                                      ((E (r ++ (eq_rec b (Vect e) u z s)))@w) =
                                      ((eq_rec (i+z) con E (i + (n + y)) (f_equal (plus i) (eq_trans' s q))
                                            (drop j (eq_rec ((j+i)+b) (Vect e) v (j+(i+(n+y)))
                                                            (eq_trans (f_equal (plus (j+i)) q) (add_assoc j i (n+y))))))@w))
                                    (fun E : con (i+b) =>
                                        eq_ind_dep b
                                            (fun (z : nat) (s : b = z) =>
                                                ((E (r ++ u))@w) =
                                                ((eq_rec (i+b) con E (i+z) (f_equal (plus i) s)
                                                            (drop j (eq_rec ((j+i)+b) (Vect e) v (j+(i+z))
                                                                            (eq_trans (f_equal (plus (j+i)) s)
                                                                                      (add_assoc j i z)))))@w))
                                            (f_equal (fun xs : e^(i+b) => (E xs)@w)
                                                (eq_trans (tkdr_app_inv2b j l (r ++ u))
                                                    (eq_trans'
                                                        (f_equal (drop j)
                                                            (eq_trans
                                                                (f_equal
                                                                    (fun xs : e^((j+i)+b) =>
                                                                        eq_rec ((j+i)+b) (Vect e) xs (j+(i+b)) (add_assoc j i b))
                                                                    (eq_trans (tkdr_app_inv (j+i) v)
                                                                        (f_equal (fun ys : e^(j+i) => ys ++ u)
                                                                            (tkdr_app_inv j (take (j + i) v)))))
                                                                (app_assoc l r u)))
                                                        (f_equal
                                                            (fun s : ((j+i)+b) = (j+(i+b)) =>
                                                                drop j (eq_rec ((j+i)+b) (Vect e) v (j+(i+b)) s))
                                                            (refl_l_id_trans (add_assoc j i b))))))
                                            (n+y) q)
                                    (m+x) p (cc m i h x C))
                            (n+(i+y)) (assoc_flip i n y)))))
                (eq_sym (p_and_ax T R w))))))
             end). *)

Definition d_OR : forall {m n i j : nat}, kon m i -> kon n j -> kon (max m n) 0
    := fun (m n i j : nat) (h : kon m i) (k : kon n j) => NOT ((NOT h) AND (NOT k)).
Infix "OR" := d_OR (at level 0) : dyn_scope.

(* so, interesting- defining (h IMPLIES k), with (h : kon m i) and (k : kon n j), as ((NOT h) OR (h AND k)) yields a term of type
    (kon (max (max n m) m) 0) rather than (kon (max n m) 0). Equivalent, obviously, but I'll have to cast it
    to keep this definition of IMPLIES *)

Definition d_IMPLIES : forall {m n i j : nat}, kon m i -> kon n j -> kon (max m n) 0
    :=  fun (m n i j : nat) (h : kon m i) (k : kon n j) (a : nat) =>
        kcast   ((h AND k) OR (NOT h)) a
                (f_equal    (fun x : nat => x+a)
                            (eq_trans   (max_comm (max m n) m)
                                        (eq_trans' (max_assoc m m n) (f_equal (fun y : nat => max y n) (max_idem m)))))
Infix "IMPLIES" := d_IMPLIES (at level 0) : dyn_scope.

(* NOTE: Now that I've swapped m and n in the max stuff for the connectives, the definitions below which depend on them
    won't work correctly! Gotta redo them to reflect the change! *)


(* Dynamic predicate stuff *)
(* moving nth,max, m_frnt,n_frnt to Vect.v *)

(* vmax takes an n-length vector of nat's and returns the smallest x:nat which is strictly greater than every nat in the vector *)
(* Defined via recursion on the length rather than the vector itself for ease of reductions *)
    (* ie for any u : Vect nat 0, (vmax u) will simplify to 0, not just when u is known to be [] *)
    (* similarly, for any u : Vect nat (S i), (vmax u) with simplify to (max (S (head u)) (vmax (tail u))), *)
    (* as opposed to only (vmax (m::l)) reducing to (max (S m) (vmax l)) for any terms m:nat & l:Vect nat i *)
    (* this is often relevant in cases where vmax is used on a variable of the type that can't be pattern-matched on *)
Fixpoint vmax {n : nat} : Vect nat n -> nat
    :=  match n as k return (Vect nat k -> nat) with
            | 0     =>  fun _ : Vect nat    0   => 0
            | S i   =>  fun v : Vect nat (S i)  => max (S (head v)) (vmax (tail v))
        end.

(* defining a generalized version of the p_i type stuff *)
(* apparently using Type here doesn't schematize the function in the way it does for Inductive def's *)
Fixpoint nary (A B : Set) (m : nat) {struct m} : Set := match m with 0 => B | S i => A -> nary A B i end.
Definition p_i : nat -> Set := nary e prop.

(* To define dy/dyn, starting with what I call the "uncurried" version of both, making dy/dyn be the "curried" versions *)

(*  Update to udy/dy- adding an additional nat argument to represent # of DR's it requires a context to have,
    Before considering the index arguments the term will receive *)
(*  This argument will go first, and it shouldn't affect udy'/dy' at all- just replacing id w/ max of this argument *)
(*  for udyn/dyn, this argument will be 0 (thus (max 0) = id, so they'll work just the same as they already did) *)

(* udy(n?)(\'?), aka "uncurried" dy(n?)(\'?), takes all of its DR's indices in a single vector at once vs as separate arguments *)
Definition udy' : (nat -> nat) -> nat -> nat -> Set
    := fun (f : nat -> nat) (m i : nat) => forall u : Vect nat m, kon (f (vmax u)) i.
Definition udy  : nat -> nat -> nat -> Set := fun n : nat => udy' (max n).

Fixpoint udyn (m : nat) {struct m} : p_i m -> udy 0 m 0
    :=  match m as k return (p_i k -> udy 0 k 0) with
            | 0     =>  fun (p : prop) (_ : Vect nat 0) (j : nat) (_ : con j) (_ : e^j) => p
            | S i   =>  fun (P : e -> p_i i) (u : Vect nat (S i)) (j : nat) (c : con ((vmax u)+j)) (v : e^((vmax u)+j)) =>
                        let (x,q) := (m_frnt (S (head u)) (vmax (tail u)) j) in
                        let (y,r) := (n_frnt (S (head u)) (vmax (tail u)) j) in
                        udyn    i           (P (nth (head u)    (eq_rec ((vmax u)+j) (Vect e) v (S ((head u)+x)) q)))
                                (tail u) y                      (eq_rec ((vmax u)+j)  con     c ((vmax (tail u))+y) r)
                                                                (eq_rec ((vmax u)+j) (Vect e) v ((vmax (tail u))+y) r)
        end.

Fixpoint dy' (f : nat -> nat) (m i : nat) {struct m} : Set
    :=  match m with
            | 0     =>  kon (f 0) i
            | S j   =>  forall m : nat, dy' (f∘(max (S m))) j i
        end.
Definition dy : nat -> nat -> nat -> Set := fun n : nat => dy' (max n).

(* udytody : forall (f : nat -> nat) (m i : nat), udy' f m i -> dy' f m i *)
(* udytody is meant as a sort of "currying" function *)
Fixpoint udytody (f : nat -> nat) (m i : nat) : udy' f m i -> dy' f m i
    :=  match m as k return (udy' f k i -> dy' f k i) with
            | 0     =>  fun  k : udy' f 0 i => k []
            | S j   =>  fun (k : udy' f (S j) i) (m : nat) => udytody (f∘(max (S m))) j i (fun l : Vect nat j => k (m::l))
        end.

Definition dyn  : forall m : nat, p_i m -> dy 0 m 0 := fun (m : nat) (P : p_i m) => udytody id m 0 (udyn m P).

(* So, this definition of dy should work, and doesn't require a starting point. Just flips associativity of max's *)
(* Fixpoint dy2 (n m i : nat) {struct m} : Set := match m with 0 => kon n i | S j => forall m : nat, dy2 (max (S m) n) j i end. *)

(* for 0≤m≤3: *)
    (* (dyn 0) :=: (fun (p : prop) (j : nat) (_ : con j) (_ : e^j) => p) *)
    (* (dyn 1) :=: (fun (P : e -> prop) (m : nat) (j : nat) (c : con (S (m+j))) (v : e^(S (m+j))) => P (nth m v)) *)
    (* (dyn 2) :=: (fun (Q : e -> e -> prop) (m : nat) (n : nat) (j : nat) (c : con (S ((max m n)+j))) (v : e^(S ((max m n)+j))) =>
                 let (x,q)  :=  (let (w,p) := (m_frnt m n j) in
                                 exist (fun x : nat => (S ((max m n)+j)) = (S (m+x))) w (f_equal S p)) in
                 let (y,r)  :=  (let (z,t) := (n_frnt m n j) in
                                 exist (fun y : nat => (S ((max m n)+j)) = (S (n+y))) z (f_equal S t)) in
                 Q  (nth m (eq_rec (S ((max m n)+j)) (Vect e) v (S (m+x)) q))
                    (nth n (eq_rec (S ((max m n)+j)) (Vect e) v (S (n+y)) r)))
            :≈: (fun (Q : e -> e -> prop) (m : nat) (n : nat) (j : nat) (c : con (S ((max m n)+j))) (v : e^(S ((max m n)+j))) =>
                 let (x,q) := (m_frnt m n j) in
                 let (y,r) := (n_frnt m n j) in
                 Q  (nth m (eq_rec ((max m n)+j) (fun z : nat => e^(S z)) v (m+x) q))
                    (nth n (eq_rec ((max m n)+j) (fun z : nat => e^(S z)) v (n+y) r))) *)
    (* (dyn 3) :=: (fun (R : e -> e -> e -> prop) (m : nat) (n : nat) (k : nat) (j : nat) (c : con ((vmax [m,n,k])+j))
                     (v : e^((vmax [m,n,k])+j)) =>
                 let (x,q)   := (let (w,p) := (m_frnt m (max n k) j) in
                                 exist (fun x : nat => (S ((max m (max n k))+j)) = (S (m+x))) w (f_equal S p)) in
                 let (y,r)   := (let (z,t) := (n_frnt m (max n k) j) in
                                 exist (fun y : nat => (S ((max m (max n k))+j)) = (S ((max n k)+y))) z (f_equal S t)) in
                 let (w,p)  :=  (let (a,s) := (m_frnt n k y) in
                                 exist (fun x : nat => (S ((max n k)+y)) = (S (n+x))) a (f_equal S s)) in
                 let (z,t)  :=  (let (b,d) := (n_frnt n k y) in
                                 exist (fun z : nat => (S ((max n k)+y)) = (S (k+z))) b (f_equal S d)) in
                 R  (nth m  (eq_rec (S ((max m (max n k))+j)) (Vect e) v (S (m+x)) q))
                    (nth n  (eq_rec (S ((max n k)+y)) (Vect e)
                                    (eq_rec (S ((max m (max n k))+j)) (Vect e) v (S ((max n k)+y)) r) (S (n+w)) p))
                    (nth k  (eq_rec (S ((max n k)+y)) (Vect e)
                                    (eq_rec (S ((max m (max n k))+j)) (Vect e) v (S ((max n k)+y)) r) (S (k+z)) t)))
            :≈: (fun (R : e -> e -> e -> prop) (m : nat) (n : nat) (k : nat) (j : nat) (c : con (S ((max m (max n k))+j)))
                     (v : e^(S ((max m (max n k))+j))) =>
                 let (x,q)  :=  (m_frnt m (max n k) j) in
                 let (y,r)  :=  (n_frnt m (max n k) j) in
                 let (w,p)  :=  (m_frnt n k y) in
                 let (z,t)  :=  (n_frnt n k y) in
                 R  (nth m  (eq_rec ((max m (max n k))+j) (fun s : nat => e^(S s)) v (m+x) q))
                    (nth n  (eq_rec ((max m (max n k))+j) (fun s : nat => e^(S s)) v (n+w) (eq_trans r p)))
                    (nth k  (eq_rec ((max m (max n k))+j) (fun s : nat => e^(S s)) v (k+z) (eq_trans r t)))) *)

(* Note- there are some more generalized versions of a few of these functions- look at extra_dy_stuff.v *)
(* as well as the dyn work files for them *)

(* context extension- defined to add arbitrary # of DR's, but the c⁺ notation will still be for +1 *)
Definition cext : forall i : nat, kon 0 i := fun (i j : nat) (c : con j) (v : e^(i+j)) => c (drop i v).
Notation "c ⁺" := (cext 1 _ c) (at level 0).

(* Dynamic Existential Quantifier *)

(* Ok…not exactly ideal. But it works, so it's good enough for now I suppose *)
(* um…isn't D's argument supposed to be 0, not (n+j)? I think that might just be the problem (but we'll see) *)
Definition EXISTS : forall {n i : nat}, dy n 1 i -> kon n (S i)
    :=  fun (n i : nat) (D : dy n 1 i) (j : nat) (c : con (n+j)) (v : e^(S (i+(n+j)))) =>
        eq_rec  (max n (S (n+j))) (fun k : nat => kon k i) (D (n+j)) (S (n+j)) (max_plus_2 n j) 0
                (eq_rec (n+j) (con∘S) c⁺ ((n+j)+0) (Zria (n+j)))
                (eq_rec (S (i+(n+j))) (Vect e) v (i+(S ((n+j)+0)))
                        (eq_trans (f_equal (S∘(plus i)) (Zria (n+j))) (Sdistr i ((n+j)+0)))).

Definition FORALL : forall {n i : nat}, dy n 1 i -> kon n 0
    := fun (n i : nat) (D : dy n 1 i) => NOT (EXISTS (fun j : nat => NOT (D j))).

Definition d_THAT : forall {m n i j : nat}, dy m 1 i -> dy n 1 j -> dy (max n m) 1 (j+i)
    :=  fun (m n i j : nat) (D : dy m 1 i) (E : dy n 1 j) (k : nat) =>
        eq_rec  (max (max n (S k)) (max m (S k))) (fun x : nat => kon x (j+i))
                ((D k) AND (E k)) (max (max n m) (S k)) (max_dist n m (S k)).
Infix "THAT" := d_THAT (at level 20) : dyn_scope.

Definition A : forall {m n i j : nat}, dy m 1 i -> dy n 1 j -> kon (max n m) (S (j+i))
    :=  fun (m n i j : nat) (D : dy m 1 i) (E : dy n 1 j) => EXISTS (D THAT E).

Definition EVERY : forall {m n i j : nat}, dy m 1 i -> dy n 1 j -> kon (max n m) 0
    :=  fun (m n i j : nat) (D : dy m 1 i) (E : dy n 1 j) =>
        FORALL (fun k : nat =>
                eq_rec  (max (max n (S k)) (max m (S k))) (fun x : nat => kon x 0)
                        ((D k) IMPLIES (E k)) (max (max n m) (S k)) (max_dist n m (S k))).

(* Example Sentence: "A donkey brays" ≡ (A DONKEY BRAY) ≡ (λc:c.λX^|c|,y.(donkey y) and (bray y)) *)
                                   (* ≡ (λj:nat.λc:con j.λv:e^(S j).(donkey (head v)) and (bray (head v))) *)


Axioms farmer donkey bray : e -> prop.
Axioms own beat : e -> e -> prop.
Axiom ch : e.
Definition DONKEY : dy 0 1 0 := (dyn 1 donkey).
    (* := fun (m j : nat) (_ : con (S (m+j))) (v : e^(S (m+j))) => donkey (nth m v) *)
Definition BRAY : dy 0 1 0 := (dyn 1 bray).
    (* := fun (m j : nat) (_ : con (S (m+j))) (v : e^(S (m+j))) => bray (nth m v) *)
Definition FARMER : dy 0 1 0 := (dyn 1 farmer).
    (* := fun (m j : nat) (_ : con (S (m+j))) (v : e^(S (m+j))) => farmer (nth m v) *)
Definition OWN  : dy 0 2 0 := (dyn 2 own).
    (* :=   fun (m n j : nat) (_ : con (S ((max m n)+j))) (v : e^(S ((max m n)+j))) =>
            let (x,q)   :=  (let (z,p) := (m_frnt m n j) in
                             exist (fun x : nat => (S ((max m n)+j)) = (S (m+x))) z (f_equal S p)) in
            let (y,r)   :=  (let (z,p) := (n_frnt m n j) in
                             exist (fun y : nat => (S ((max m n)+j)) = (S (n+y))) z (f_equal S p)) in
            own (nth m (eq_rec (S ((max m n)+j)) (Vect e) v (S (m+x)) q))
                (nth n (eq_rec (S ((max m n)+j)) (Vect e) v (S (n+y)) r)) *)
    (* :≈   fun (m n j : nat) (_ : con (S ((max m n)+j))) (v : e^(S ((max m n)+j))) =>
            let (x,q)   := (m_frnt m n j) in
            let (y,r)   := (n_frnt m n j) in
            own (nth m (eq_rec ((max m n)+j) (fun z : nat => e^(S z)) v (m+x) q))
                (nth n (eq_rec ((max m n)+j) (fun z : nat => e^(S z)) v (n+y) r)) *)
Definition BEAT : dy 0 2 0 := (dyn 2 beat).
    (* :=   fun (m n j : nat) (_ : con (S ((max m n)+j))) (v : e^(S ((max m n)+j))) =>
            let (x,q)   :=  (let (z,p) := (m_frnt m n j) in
                             exist (fun x : nat => (S ((max m n)+j)) = (S (m+x))) z (f_equal S p)) in
            let (y,r)   :=  (let (z,p) := (n_frnt m n j) in
                             exist (fun y : nat => (S ((max m n)+j)) = (S (n+y))) z (f_equal S p)) in
            beat    (nth m (eq_rec (S ((max m n)+j)) (Vect e) v (S (m+x)) q))
                    (nth n (eq_rec (S ((max m n)+j)) (Vect e) v (S (n+y)) r)) *)
    (* :≈   fun (m n j : nat) (_ : con (S ((max m n)+j))) (v : e^(S ((max m n)+j))) =>
            let (x,q)   := (m_frnt m n j) in
            let (y,r)   := (n_frnt m n j) in
            beat    (nth m (eq_rec ((max m n)+j) (fun z : nat => e^(S z)) v (m+x) q))
                    (nth n (eq_rec ((max m n)+j) (fun z : nat => e^(S z)) v (n+y) r)) *)

(* A (dyn 1 donkey) (dyn 1 bray) *)

(* so these are predicted one entity is both the farmer and the donkey… *)

Definition ADON : dy 0 1 1  := fun i : nat => @A 0 (S i) 0 0 DONKEY (OWN i).
Definition FTA  : dy 0 1 1  := @d_THAT 0 0 0 1 FARMER ADON.
Definition BT   : dy 0 2 0  := fun a b : nat => eq_rec (max b a) (fun x : nat => kon (S x) 0) (BEAT b a) (max a b) (max_comm b a).


(* Definition EFWOADBI : dy 0 1 0 := fun n : nat => @EVERY 0 (S n) 1 0 FTA (BT n). *)
    (* :=  fun n : nat =>
        EVERY   (FARMER THAT (fun i : nat => A DONKEY (OWN i)))
                (fun i : nat => eq_rec (max i n) (fun x : nat => kon (S x) 0) (BEAT i n) (max n i) (max_comm i n)). *)

(* shouldn't this be kon 0 0? *)
(* should be (@EVERY 0 0 1 0) *)
Definition EFWOADBI0 : kon 0 0
    :=  @EVERY  0 0 1 0
                (@d_THAT 0 0 0 1 FARMER (fun i : nat => @A 0 (S i) 0 0 DONKEY (OWN i)))
                (fun i : nat => eq_rec (max i 0) (fun x : nat => kon (S x) 0) (BEAT i 0) i (max_comm i 0)).
    (*  :=  (EFWOADBI 0). *)
    (*  :=  EVERY   (FARMER THAT (fun i : nat => A DONKEY (OWN i)))
                    (fun i : nat => eq_rec (max i 0) (fun x : nat => kon (S x) 0) (BEAT i 0) i (max_comm i 0)). *)

(* EFWOADBI    : dy 0 1 0
            : forall m j : nat, con (S (m+j)) -> con (S (m+j))
            : forall m : nat, kon (S m) 0

    @EVERY : forall m n i j : nat, dy m 1 i -> dy n 1 j -> kon (max n m) 0
    (@EVERY 0 0 1 0 FTA (BT 0)) : kon 0 0 *)

Definition efnil : prop := EFWOADBI0 0 (fun _ : e^0 => truth) [].
(* Eval compute in efnil.
    := (not (p_exists ent
         (fun x : e => not (not ((not (p_exists ent (fun y : e => ((farmer x) and ((donkey x) and (own y x))) and (beat y y))))
                            and (not (not (p_exists ent (fun z : e => (farmer x) and ((donkey x) and (own z x))))))))))) *)
(* Still bad… *)



(*  Eval compute in (EFWOADBI 0 0 (fun _ : e^0 => truth) [ch]).
    =   not (p_exists ent
                    (fun x : e =>
                     not (not ((not (p_exists ent (fun y : e => ((farmer ch) and ((donkey ch) and (own x ch))) and (beat x y))))
                               and (not (not (p_exists ent (fun _ : e => (farmer ch) and ((donkey ch) and (own x ch))))))))))
    ≈   not (p_exists ent
                    (fun x : e =>
                     (not (p_exists ent (fun y : e => ((farmer ch) and ((donkey ch) and (own x ch))) and (beat x y))))
                      and (p_exists ent (fun _ : e => (farmer ch) and ((donkey ch) and (own x ch))))))
     : prop *)

(* ∀w:world.[(EFWOADBI 0 0 (fun _ : e^0 => truth) [ch])@w
                    <-> ∀x:e.[((farmer ch)@w && ((donkey ch)@w && (own x ch)@w)) ~> ∃y:e.[(beat x y)@w]]] *)



