(* name update:
    old kon will now be called xon (eXact contents),
    old update will be the new kon *)


(*  donkey_sentence_4.v- simplifying the type of AND, etc, by only quantifying over one presupposition count,
    removing a bunch of maxes *)

(* id, comp, flip, eq_ind_dep, eq_trans', tnf, feq, feq2, feq3 *)
    Definition id : forall {A : Type}, A -> A := fun (A : Type) (x : A) => x.
    Definition comp : forall {A B C:Type},(B->C)->(A->B)->A->C := fun (A B C : Type) (f : B -> C) (g : A -> B) (x : A) => f (g x).
    Infix "∘" := comp (at level 20).
    Definition flip : forall {A B C:Type},(A->B->C)->B->A->C := fun (A B C : Type) (f : A -> B -> C) (y : B) (x : A) => f x y.
    Definition eq_ind_dep : forall {A:Type} (x:A) (P:forall z:A, x = z -> Prop), P x eq_refl -> forall (y:A) (e:x=y), P y e
        :=  fun (A : Type) (x : A) (P : forall z : A, x = z -> Prop) (p : P x eq_refl) (y : A) (e : x = y) =>
            match e as d in (_ = z) return (P z d) with eq_refl => p end.
    Definition eq_trans' : forall {A : Type} {x y z : A}, x = y -> x = z -> y = z
        :=  fun (A : Type) (x y z : A) (u : x = y) (v : x = z) => eq_ind x (flip eq z) v y u.
    Definition tnf : true <> false := eq_ind true (fun b : bool => if b then True else False) I false.

    Definition feq  : forall {A B : Type} (f : A -> B) {x y : A}, x = y -> (f x) = (f y)
        :=  fun (A B : Type) (f : A -> B) (x : A) => eq_ind x (fun z : A => (f x) = (f z)) eq_refl.
    Definition feq2 : forall {A B C : Type} (f : A -> B -> C) {x a : A} {y b : B}, x = a -> y = b -> (f x y) = (f a b)
        :=  fun (A B C : Type) (f : A -> B -> C) (x a : A) (y b : B) =>
            eq_ind x (fun z : A => y = b -> (f x y) = (f z b)) (feq (f x)) a.
    Definition feq3 : forall {A B C D : Type} (f : A -> B -> C -> D) {x a : A} {y b : B} {z c : C},
            x = a -> y = b -> z = c -> (f x y z) = (f a b c)
            :=  fun (A B C D : Type) (f : A -> B -> C -> D) (x a : A) (y b : B) (z c : C) =>
                eq_ind  x (fun d : A => y = b -> z = c -> (f x y z) = (f d b c)) (feq2 (f x)) a.

(* CDS_prims.v *)
    Axiom e prop world      : Set.
    Axiom tv                : prop -> world -> bool.
    Axiom truth             : prop.
    Axiom p_not             : prop -> prop.
    Axiom p_and p_implies   : prop -> prop -> prop.

    Section Statterm.
        Inductive statterm : Set := ent : statterm | prp : statterm | func : statterm -> statterm -> statterm.
        Fixpoint Sns (s : statterm) : Set := match s with ent => e | prp => prop | func a b => Sns a -> Sns b end.
        (* for the record, Ext and ext_at aren't necessary for the dynamic stuff *)
        Fixpoint Ext (s : statterm) : Set := match s with ent => e | prp => bool | func a b => Sns a -> Ext b end.
        Fixpoint ext_at (s : statterm) : Sns s -> world -> Ext s
            :=  match s as t return (Sns t -> world -> Ext t) with
                    | ent       => fun (x : e) (_ : world) => x
                    | prp       => tv
                    | func a b  => fun (f : Sns a -> Sns b) (w : world) (x : Sns a) => ext_at b (f x) w
                end.
    End     Statterm.

    Axiom p_exists p_forall : forall s : statterm, (Sns s -> prop) -> prop.

    Module Import   Sem_notations.
        Infix "and"         := p_and            (at level 80)   : sem_scope.
        Infix "implies"     := p_implies        (at level 80)   : sem_scope.
        Notation "'not' p"  := (p_not p)        (at level 80)   : sem_scope.
        Notation "p @ w"    := (tv p w)         (at level 30)   : sem_scope.
        Open Scope sem_scope.
        Infix    "~>"       := implb            (at level 50)   : bool_scope.
        Notation "-~ x"     := (negb x)         (at level 50)   : bool_scope.
        Open Scope bool_scope.
    End             Sem_notations.

    Definition s_that   : (e -> prop) -> (e -> prop) -> e -> prop   := fun (P Q : e -> prop) (x : e) => (P x) and (Q x).
    Infix "that"        := s_that (at level 80) : sem_scope.
    Definition pex      : (e -> prop) -> prop   := p_exists ent.
    Definition pfa      : (e -> prop) -> prop   := p_forall ent.
    Definition some     : (e -> prop) -> (e -> prop) -> prop := fun P Q : e -> prop => pex (P that Q).
    Definition every    : (e -> prop) -> (e -> prop) -> prop := fun P Q : e -> prop => pfa (fun x : e => (P x) implies (Q x)).

    Definition p_entails : prop -> prop -> Prop := fun p q : prop => forall w : world, p@w = true -> q@w = true.
    Infix "entails" := p_entails (at level 80) : sem_scope.
    Definition p_equiv : prop -> prop -> Prop := fun p q : prop => (p entails q) /\ (q entails p).
    Infix "≡" := p_equiv (at level 80) : sem_scope.

(* extensions.v (plus relevant extensional stuff from CDS_prims.v) *)
    Section prop_axioms.
        Axiom p_and_ax      : forall (p q : prop) (w : world), (p and q)@w = (p@w && q@w).
        Axiom p_implies_ax  : forall (p q : prop) (w : world), (p implies q)@w = (p@w ~> q@w).
        Axiom p_not_ax      : forall (p   : prop) (w : world), (not p)@w = -~(p@w).
        Axiom truth_ax      : forall w : world, truth@w = true.
        Axiom p_exists_ax   : forall (s : statterm) (R : Sns s -> prop) (w : world),
            ((p_exists s R)@w = true) <-> ~(forall x : Sns s, (R x)@w = false).
        Axiom p_forall_ax   : forall (s : statterm) (R : (Sns s) -> prop) (w : world),
            ((p_forall s R)@w = true) <-> (forall x : Sns s, (R x)@w = true).
    End prop_axioms.

    Section prop_Theorems.
        Definition dne          : forall p : prop, (not (not p)) entails p
            :=  fun (p : prop) (w : world) (e : (not (not p))@w = true) =>
                (if p@w as b return (-~(-~b) = true -> b = true) then id else id)
                (eq_trans' (eq_trans (p_not_ax (not p) w) (feq negb (p_not_ax p w))) e).

        Definition int_eq : forall p q : prop, (forall w : world, p@w = q@w) -> p ≡ q
            :=  fun (p q : prop) (f : forall w : world, p@w = q@w) =>
                conj (fun w : world => eq_trans' (f w)) (fun w : world => eq_trans (f w)).
    End prop_Theorems.

(* Vect.v *)
    Inductive Vect (A : Type) : nat -> Type := vnil : Vect A 0 | vcons : forall n : nat, A -> Vect A n -> Vect A (S n).
    Arguments vnil  {A}.
    Arguments vcons {A} {n} _ _.

    Module Import   VectNotes.
        Notation "[]" := vnil (at level 0) : vect_scope.
        Infix "::" := vcons (at level 60, right associativity) : vect_scope.
        Open Scope vect_scope.
        Notation "[ x ]" := ((x :: [])) (at level 0) : vect_scope.
        Notation "[ x , .. , y ]" := ((vcons x .. (y :: []) ..)) (at level 0) : vect_scope.
    End             VectNotes.

    Definition head : forall {A : Type} {n : nat}, Vect A (S n) -> A
        :=  fun (A : Type) (n : nat) (v : Vect A (S n)) =>
            match v in (Vect _ m) return (if m then unit else A) with [] => tt | x :: _ => x end.

    Definition tail : forall {A : Type} {n : nat}, Vect A (S n) -> Vect A n
        :=  fun (A : Type) (n : nat) (v : Vect A (S n)) =>
            match v in (Vect _ m) return (match m with 0 => unit | S k => Vect A k end) with [] => tt | _ :: xs => xs end.

    Fixpoint append {A : Type} {m n : nat} (u : Vect A m) (v : Vect A n) : Vect A (m+n)
        := match u in (Vect _ i) return (Vect A (i+n)) with [] => v | x :: l => x::(append l v) end.
    Infix "++" := append (at level 60, right associativity) : vect_scope.

    Fixpoint take (A : Type) (m n : nat) {struct m} : Vect A (m+n) -> Vect A m
        :=  match m as k return (Vect A (k+n) -> Vect A k) with
                | 0     => fun _ : Vect A n => []
                | S i   => fun v : Vect A (S (i+n)) => (head v)::(take A i n (tail v))
            end.
    Fixpoint drop (A : Type) (m n : nat) {struct m} : Vect A (m+n) -> Vect A n
        :=  match m as k return (Vect A (k+n) -> Vect A n) with
                | 0     => id
                | S i   => fun v : Vect A (S (i+n)) => drop A i n (tail v)
            end.
    Arguments take {A} m {n} v.
    Arguments drop {A} m {n} v.
    (* split_at? *)

    Fixpoint nth {A : Type} (m : nat) {n : nat} : Vect A (S (m+n)) -> A
        := match m as i return (Vect A (S (i+n)) -> A) with 0 => head | S i => fun v : Vect A (S (S (i+n))) => nth i (tail v) end.

    (* h_frnt/k_frnt below the proofs section- need to move them below the proofs section b/c they rely on Zria/Zrix *)

    Definition vcast : forall {A : Type} {m : nat}, Vect A m -> forall {n : nat}, m = n -> Vect A n
        := fun (A : Type) (m : nat) => eq_rect m (Vect A).

(* max and vmax *)
    Fixpoint max (m n : nat) {struct m} : nat
        := match m with 0 => n | S i => S (match n with 0 => i | S j => max i j end) end.

    Fixpoint vmax {n : nat} : Vect nat n -> nat
        :=  match n as k return (Vect nat k -> nat) with
                | 0     =>  fun _ : Vect nat    0   => 0
                | S i   =>  fun v : Vect nat (S i)  => max (S (head v)) (vmax (tail v))
            end.

(* Vect.v/DyCG.v Proofs *)
    (* meta-proofs over equality *)
        Definition refl_l_id_trans : forall {A : Type} {x y : A} (e : x = y), e = (eq_trans eq_refl e)
            := fun (A : Type) (x : A) => eq_ind_dep x (fun (z : A) (d : x = z) => d = eq_trans eq_refl d) eq_refl.
        Definition refl_r_id_trans': forall {A : Type} {x y : A} (e : x = y), (eq_sym e) = (eq_trans' e eq_refl)
            := fun (A : Type) (x : A) => eq_ind_dep x (fun (z : A) (d : x = z) => (eq_sym d) = (eq_trans' d eq_refl)) eq_refl.
        Definition feq_comp : forall {A B C : Type} (f : B -> C) (g : A -> B) {x y : A} (e : x = y),
            (feq f (feq g e)) = (feq (f∘g) e)
            :=  fun (A B C : Type) (f : B -> C) (g : A -> B) (x : A) =>
                eq_ind_dep x (fun (z : A) (d : x = z) => (feq f (feq g d)) = (feq (f∘g) d)) eq_refl.
        Definition feqovertrans : forall {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z),
            (eq_trans (feq f p) (feq f q)) = (feq f (eq_trans p q))
            :=  fun (A B : Type) (f : A -> B) (x y z : A) (p : x = y) =>
                eq_ind_dep y (fun (k : A) (q : y = k) => (eq_trans (feq f p) (feq f q)) = (feq f (eq_trans p q))) eq_refl z.
        Definition eq_rect_f1   : forall {A B : Type} (P : A -> Type) {x : A} (f : P x -> B) {y : A} (e : x = y) (p : P y),
            (eq_rect x (fun z : A => P z -> B) f y e p) = (f (eq_rect y P p x (eq_sym e)))
            :=  fun (A B : Type) (P : A -> Type) (x : A) (f : P x -> B) =>
                eq_ind_dep  x (fun (y : A) (d : x = y) =>
                               forall p : P y, (eq_rect x (fun z : A => P z -> B) f y d p) = (f (eq_rect y P p x (eq_sym d))))
                            (fun p : P x => eq_refl).
        Definition eq_rect_f2   : forall {A B : Type} (P : A -> Type) {x : A} (f : B -> P x) (b : B) {y : A} (e : x = y),
            (eq_rect x (fun z : A => B -> P z) f y e b) = (eq_rect x P (f b) y e)
            :=  fun (A B : Type) (P : A -> Type) (x : A) (f : B -> P x) (b : B) =>
                eq_ind_dep  x (fun (y : A) (d : x = y) => (eq_rect x (fun z : A => B -> P z) f y d b) = (eq_rect x P (f b) y d))
                            eq_refl.
        Definition eq_rect_f3   : forall {A : Type} (P Q : A -> Type) {x : A} (f : P x -> Q x) {y : A} (e : x = y) (p : P y),
            (eq_rect x (fun z : A => P z -> Q z) f y e p) = (eq_rect x Q (f (eq_rect y P p x (eq_sym e))) y e)
            :=  fun (A : Type) (P Q : A -> Type) (x : A) (f : P x -> Q x) =>
                eq_ind_dep x (fun (y : A) (d : x = y) => forall p : P y,
                                (eq_rect x (fun z : A => P z -> Q z) f y d p) = (eq_rect x Q (f (eq_rect y P p x (eq_sym d))) y d))
                    (fun p : P x => eq_refl).
        Definition eq_rect_feq  : forall {A B : Type} (P : B -> Type) (f : A -> B) {x : A} (p : P (f x)) {y : A} (d : x = y),
            (eq_rect (f x) P p (f y) (feq f d)) = (eq_rect x (P∘f) p y d)
            :=  fun (A B : Type) (P : B -> Type) (f : A -> B) (x : A) (p : P (f x)) =>
                eq_ind_dep x (fun (y : A) (d : x = y) => (eq_rect (f x) P p (f y) (feq f d)) = (eq_rect x (P∘f) p y d)) eq_refl.
        Definition trans_inv1   : forall {A : Type} {x y : A} (p : x = y), (eq_trans (eq_sym p) p) = eq_refl
            := fun (A : Type) (x : A) => eq_ind_dep x (fun (y : A) (p : x = y) => (eq_trans (eq_sym p) p) = eq_refl) eq_refl.
        Definition trans_inv2   : forall {A : Type} {x y : A} (p : x = y), (eq_trans p (eq_sym p)) = eq_refl
            := fun (A : Type) (x : A) => eq_ind_dep x (fun (y : A) (p : x = y) => (eq_trans p (eq_sym p)) = eq_refl) eq_refl.
        Definition trans'_inv   : forall {A : Type} {x y : A} (p : x = y), (eq_trans' p p) = eq_refl
            := fun (A : Type) (x : A) => eq_ind_dep x (fun (y : A) (p : x = y) => (eq_trans' p p) = eq_refl) eq_refl.
        Definition feqoversym : forall {A B : Type} (f : A -> B) {x y : A} (d : x = y), (feq f (eq_sym d)) = (eq_sym (feq f d))
            :=  fun (A B : Type) (f : A -> B) (x : A) =>
                eq_ind_dep x (fun (y : A) (d : x = y) => (feq f (eq_sym d)) = (eq_sym (feq f d))) eq_refl.

    (* Basic nat/addition proofs *)
        Definition Zria         : forall n : nat, (n+0) = n
            := nat_ind (fun n : nat => (n+0) = n) eq_refl (fun i : nat => feq S).
        Definition Sdistr       : forall m j : nat, (S (m+j)) = (m+(S j))
            := fun m j : nat => nat_ind (fun i : nat => (S (i+j)) = (i+(S j))) eq_refl (fun i : nat => feq S) m.
        Definition add_comm     : forall m n : nat, (m+n) = (n+m)
            :=  fun m : nat =>
                nat_ind (fun n : nat => (m+n) = (n+m)) (Zria m)
                        (fun (j : nat) (e : (m+j) = (j+m)) => eq_trans' (Sdistr m j) (feq S e)).
        Definition add_assoc    : forall m n k : nat, (m+(n+k)) = ((m+n)+k)
            := fun m n k : nat => nat_ind (fun i : nat => (i+(n+k)) = ((i+n)+k)) eq_refl (fun i : nat => feq S) m.
        Definition assoc_flip   : forall m n k : nat, ((m+n)+k) = ((m+k)+n)
            := fun m n k : nat => nat_ind (fun i : nat => ((i+n)+k) = ((i+k)+n)) (add_comm n k) (fun i : nat => feq S) m.

    (* Vect proofs *)
        Definition Vect_form : forall {A : Type} {n : nat} (v : Vect A n),
                                (match n as m return (Vect A m -> Prop)
                                 with 0 => eq [] | S i => fun u : Vect A (S i) => ((head u)::(tail u)) = u end) v
            :=  fun (A : Type) (n : nat) (v : Vect A n) =>
                match v as u in (Vect _ k)
                return ((match k as m return (Vect A m -> Prop)
                         with 0 => eq [] | S i => fun l : Vect A (S i) => ((head l)::(tail l)) = l end) u)
                with [] => eq_refl | x::xs => eq_refl end.

        (* "vcast narrowing" *)
        Definition vcstnrw      : forall {A : Type} {m : nat} (v : Vect A (S m)) {n : nat} (e : m = n),
            (vcast v (feq S e)) = ((head v)::(vcast (tail v) e))
            :=  fun (A : Type) (m : nat) (v : Vect A (S m)) =>
                eq_ind_dep m    (fun (n : nat) (d : m = n) => (vcast v (feq S d)) = ((head v)::(vcast (tail v) d)))
                                (eq_sym (Vect_form v)).
        Definition vcsttrans    : forall {A : Type} {m : nat} (v : Vect A m) {n k : nat} (p : m = n) (q : n = k),
            (vcast (vcast v p) q) = (vcast v (eq_trans p q))
            :=  fun (A : Type) (m : nat) (v : Vect A m) (n k : nat) (p : m = n) =>
                eq_ind_dep n (fun (z : nat) (q : n = z) => (vcast (vcast v p) q) = (vcast v (eq_trans p q))) eq_refl k.
        Definition vcstinj      : forall {A : Type} {m : nat} (u v : Vect A m) {n : nat} (e : m = n),
            (vcast u e) = (vcast v e) -> u = v
            :=  fun (A : Type) (m : nat) (u v : Vect A m) =>
                eq_ind_dep m (fun (n : nat) (d : m = n) => (vcast u d) = (vcast v d) -> u = v) id.

        Definition take_assoc   : forall {A : Type} (m n k : nat) (v : Vect A (m+(n+k))),
            (take m v) = (take m (take (m+n) (vcast v (add_assoc m n k))))
            :=  fun (A : Type) (m n k : nat) =>
                nat_ind (fun i : nat => forall v : Vect A (i+(n+k)),
                            (take i v) = (take i (take (i+n) (vcast v (add_assoc i n k)))))
                        (fun _ : Vect A (n+k) => eq_refl)
                        (fun (i : nat)
                             (f : forall r : Vect A (i+(n+k)), (take i r) = (take i (take (i+n) (vcast r (add_assoc i n k)))))
                             (v : Vect A (S (i+(n+k)))) =>
                            eq_trans    (feq (vcons (head v)) (f (tail v)))
                                        (eq_sym (feq    (fun u : Vect A (S ((i+n)+k)) => (head u)::(take i (take (i+n) (tail u))))
                                                        (vcstnrw v (add_assoc i n k)))))
                        m.
        Definition drop_assoc   : forall {A : Type} (m n k : nat) (v : Vect A ((m+n)+k)),
            (drop (m+n) v) = (drop n (drop m (vcast v (eq_sym (add_assoc m n k)))))
            :=  fun (A : Type) (m n k : nat) =>
                nat_ind (fun i : nat => forall v : Vect A ((i+n)+k),
                            (drop (i+n) v) = (drop n (drop i (vcast v (eq_sym (add_assoc i n k))))))
                        (fun v : Vect A (n+k) => eq_refl)
                        (fun (i : nat) (f : forall r : Vect A ((i+n)+k),
                                                (drop (i+n) r) = (drop n (drop i (vcast r (eq_sym (add_assoc i n k))))))
                             (v : Vect A (S ((i+n)+k))) =>
                            eq_trans    (f (tail v))
                                        (eq_trans'  (feq    (fun u : Vect A (S (i+(n+k))) => drop n (drop i (tail u)))
                                                            (vcstnrw v (eq_sym (add_assoc i n k))))
                                                    (feq    (fun d : (S ((i+n)+k)) = (S (i+(n+k))) =>
                                                                drop n (drop i (tail (vcast v d))))
                                                            (feqoversym S (add_assoc i n k)))))
                        m.
        Definition take_assoc2  : forall {A : Type} (m n k : nat) (v : Vect A (m+(n+k))),
            ((take m v) ++ (take n (drop m v))) = (take (m+n) (vcast v (add_assoc m n k)))
            :=  fun (A : Type) (m n k : nat) =>
                nat_ind (fun i : nat => forall v : Vect A (i+(n+k)),
                            ((take i v) ++ (take n (drop i v))) = (take (i+n) (vcast v (add_assoc i n k))))
                        (fun v : Vect A (n+k) => eq_refl)
                        (fun (i : nat) (f : forall r : Vect A (i+(n+k)),
                                            ((take i r) ++ (take n (drop i r))) = (take (i+n) (vcast r (add_assoc i n k))))
                             (v : Vect A (S (i+(n+k)))) =>
                            eq_trans    (feq    (vcons (head v)) (f (tail v)))
                                        (eq_sym (feq    (fun u : Vect A (S ((i+n)+k)) => (head u)::(take (i+n) (tail u)))
                                                        (vcstnrw v (add_assoc i n k)))))
                        m.

        Definition Nriap        : forall {A : Type} {n : nat} (v : Vect A n), v = (vcast (v ++ []) (Zria n))
            :=  fun A : Type =>
                Vect_ind A  (fun (n : nat) (v : Vect A n) => v = (vcast (v ++ []) (Zria n))) eq_refl
                            (fun (i : nat) (x : A) (r : Vect A i) (e : r = (vcast (r ++ []) (Zria i))) =>
                                eq_trans    (feq (vcons x) e)
                                            (eq_ind_dep (i+0)
                                                (fun (z : nat) (d : (i+0) = z) =>
                                                    (x::(vcast (r ++ []) d)) = (vcast (x::(r ++ [])) (feq S d)))
                                                eq_refl i (Zria i))).
        Definition Nriap2       : forall {A : Type} {n : nat} (v : Vect A (n+0)), ((vcast v (Zria n)) ++ []) = v
            :=  fun A : Type =>
                nat_ind (fun n : nat => forall v : Vect A (n+0), ((vcast v (Zria n)) ++ []) = v)
                        (fun v : Vect A 0 => eq_ind [] (fun u : Vect A 0 => (u ++ []) = u) eq_refl v (Vect_form v))
                        (fun (j : nat) (f : forall r : Vect A (j+0), ((vcast r (Zria j)) ++ []) = r) (v : Vect A (S (j+0))) =>
                            eq_trans    (feq (flip append []) (vcstnrw v (Zria j)))
                                        (eq_trans (feq (vcons (head v)) (f (tail v))) (Vect_form v))).

        Definition tkdr_app_inv : forall {A : Type} (m : nat) {n : nat} (v : Vect A (m+n)), v = ((take m v) ++ (drop m v))
            :=  fun (A : Type) (m n : nat) =>
                nat_ind (fun i : nat => forall v : Vect A (i+n), v = ((take i v) ++ (drop i v)))
                        (@eq_refl (Vect A n))
                        (fun (i : nat) (f : forall r : Vect A (i+n), r = ((take i r) ++ (drop i r))) (v : Vect A (S (i+n))) =>
                            eq_trans' (Vect_form v) (feq (vcons (head v)) (f (tail v)))) m.

        (* take/drop of a vector (l++r) is equal to l/r, respectively *)
        Definition tkdr_app_inv2a : forall {A : Type} (m : nat) {n : nat} (u : Vect A m) (v : Vect A n), u = (take m (u ++ v))
            :=  fun (A : Type) (m n : nat) (u : Vect A m) (v : Vect A n) =>
                Vect_ind A  (fun (i : nat) (l : Vect A i) => l = (take i (l ++ v))) eq_refl
                            (fun (i : nat) (x : A) (l : Vect A i) => feq (vcons x)) m u.
        Definition tkdr_app_inv2b : forall {A : Type} (m : nat) {n : nat} (u : Vect A m) (v : Vect A n), v = (drop m (u ++ v))
            :=  fun (A : Type) (m n : nat) (u : Vect A m) (v : Vect A n) =>
                Vect_ind A  (fun (i : nat) (l : Vect A i) => v = (drop i (l ++ v))) eq_refl
                            (fun (i : nat) (_ : A) (l : Vect A i) => id) m u.

        (* functional versions! *)
        Definition tkdr_app_inv3a : forall {A : Type} {n m : nat} (v : Vect A m),
            (fun u : Vect A n => take m (v ++ u)) = (fun _ : Vect A n => v)
            :=  fun (A : Type) (n : nat) =>
                Vect_ind A  (fun (m : nat) (v : Vect A m) => (fun u : Vect A n => take m (v ++ u)) = (fun _ : Vect A n => v))
                            eq_refl (fun (i : nat) (x : A) (l : Vect A i) => feq (comp (vcons x))).
        Definition tkdr_app_inv3b : forall {A : Type} {n m : nat} (v : Vect A m), (fun u : Vect A n => drop m (v ++ u)) = id
            :=  fun (A : Type) (n : nat) =>
                Vect_ind A  (fun (m : nat) (v : Vect A m) => (fun u : Vect A n => drop m (v ++ u)) = id)
                            eq_refl (fun (i : nat) (x : A) (l : Vect A i) => id).

        Definition vapp0        : forall {A : Type} {m : nat} (v : Vect A (m+0)), ((take m v) ++ []) = v
            :=  fun A : Type =>
                nat_ind (fun m : nat => forall v : Vect A (m+0), ((take m v) ++ []) = v) Vect_form
                        (fun (i : nat) (f : forall r : Vect A (i+0), ((take i r) ++ []) = r) (v : Vect A (S (i+0))) =>
                            eq_trans (feq (vcons (head v)) (f (tail v))) (Vect_form v)).

        Definition vcsttke      : forall {A : Type} {m n : nat} (v : Vect A (m+n)) {k : nat} (d : m = k),
            (vcast (take m v) d) = (take k (vcast v (feq (flip plus n) d)))
            :=  fun (A : Type) (m n : nat) (v : Vect A (m+n)) =>
                eq_ind_dep  m (fun (k : nat) (d : m = k) => (vcast (take m v) d) = (take k (vcast v (feq (flip plus n) d))))
                            eq_refl.

    (* Max Proofs *)
        Definition Zrix     : forall m : nat, (max m 0) = m
            := fun m : nat => match m as i return ((max i 0) = i) with 0 => eq_refl | S i => eq_refl end.
        Definition max_plus : forall m n : nat, (max m (m+n)) = (m+n)
            := fun m n : nat => nat_ind (fun i : nat => (max i (i+n)) = (i+n)) eq_refl (fun i : nat => feq S) m.
        Definition max_idem : forall m : nat, (max m m) = m
            := nat_ind (fun m : nat => (max m m) = m) eq_refl (fun i : nat => feq S).
        Definition max_assoc: forall m n p : nat, (max (max m n) p) = (max m (max n p))
            :=  nat_ind (fun m : nat => forall n p : nat, (max (max m n) p) = (max m (max n p)))
                        (fun n p : nat => eq_refl)
                        (fun (i : nat) (f : forall j k : nat, (max (max i j) k) = (max i (max j k))) (n p : nat) =>
                            match n as j,p as k return ((max (max (S i) j) k) = (max (S i) (max j k)))
                            with S j,S k => feq S (f j k) | _,_ => eq_refl end).
        Definition max_comm : forall m n : nat, (max m n) = (max n m)
            :=  nat_ind (fun m : nat => forall n : nat, (max m n) = (max n m)) (fun n : nat => eq_sym (Zrix n))
                        (fun (i : nat) (f : forall j : nat, (max i j) = (max j i)) (n : nat) =>
                            match n as j return ((max (S i) j) = (max j (S i))) with 0 => eq_refl | S j => feq S (f j) end).

        Fixpoint max_dist (m n k : nat) {struct k} : (max (max m k) (max n k)) = (max (max m n) k)
            :=  match m as x,n as y,k as z return ((max (max x z) (max y z)) = (max (max x y) z)) with
                    | 0,0,0         => eq_refl
                    | 0,0,S z       => feq S (max_dist 0 0 z)
                    | 0,S y,0       => eq_refl
                    | 0,S y,S z     => feq S (max_dist 0 y z)
                    | S x,0,0       => eq_refl
                    | S x,0,S z     => feq S (eq_trans (max_dist x 0 z) (feq (flip max z) (Zrix x)))
                    | S x,S y,0     => eq_refl
                    | S x,S y,S z   => feq S (max_dist x y z)
                end.
        Definition max_plus_2 : forall m n : nat, (S (m+n)) = (max m (S (m+n)))
            := fun m n : nat => nat_ind (fun i : nat => (S (i+n)) = (max i (S (i+n)))) eq_refl (fun i : nat => feq S) m.

        Definition max_add      : forall m n k : nat, (max (k+m) (k+n)) = (k+(max m n))
            := fun m n : nat => nat_ind (fun k : nat => (max (k+m) (k+n)) = (k+(max m n))) eq_refl (fun k : nat => feq S).
        Definition max_k_plus   : forall m n k : nat, (max (m+k) (n+k)) = ((max m n)+k)
            :=  fun m n k : nat =>
                eq_trans (feq2 max (add_comm m k) (add_comm n k)) (eq_trans (max_add m n k) (add_comm k (max m n))).

        Definition max_succ     : forall m : nat, (max m (S m)) = (S m)
            := nat_ind (fun m : nat => (max m (S m)) = (S m)) eq_refl (fun i : nat => feq S).

    (* Other *)
        Definition andb_assoc : forall b c d : bool, (b && (c && d)) = ((b && c) && d)
            := fun b c d : bool => if b as s return ((s && (c && d)) = ((s && c) && d)) then eq_refl else eq_refl.
        Definition feqSZria     : forall (m n : nat) (p : m = n), (feq (flip plus 0) (feq S p)) = (feq S (feq (flip plus 0) p))
            := fun (m n : nat) (p : m = n) => eq_trans (feq_comp (flip plus 0) S p) (eq_sym (feq_comp S (flip plus 0) p)).
        Definition dist0isidem  : forall m : nat, (max_dist 0 0 m) = (max_idem m)
            := nat_ind (fun m : nat => (max_dist 0 0 m) = (max_idem m)) eq_refl (fun i : nat => feq (feq S)).
        Definition Zrvsadas00   : forall m : nat, (Zria (m+0)) = (eq_sym (add_assoc m 0 0))
            := nat_ind  (fun m : nat => (Zria (m+0)) = (eq_sym (add_assoc m 0 0))) eq_refl
                        (fun (i : nat) (d : (Zria (i+0)) = (eq_sym (add_assoc i 0 0))) =>
                            eq_trans (feq (feq S) d) (feqoversym S (add_assoc i 0 0))).

(* h_frnt/k_frnt *)
    Fixpoint h_frnt (m n : nat)   {struct m} : {x : nat | (max m n) = (m+x)}
        :=  match m as i,n as j return {x : nat | (max i j) = (i+x)} with
                | 0,j       =>  exist (eq j) j eq_refl
                | i,0       =>  exist (fun x : nat => (max i 0) = (i+x)) 0 (eq_trans (Zrix i) (eq_sym (Zria i)))
                | S i,S j   =>  let (x,p) := (h_frnt i j) in (exist (fun y : nat => (S (max i j)) = (S (i+y))) x (feq S p))
            end.
    Fixpoint k_frnt (m n : nat)   {struct m} : {y : nat | (max m n) = (n+y)}
        :=  match m as i,n as j return {y : nat | (max i j) = (j+y)} with
                | 0,j       =>  exist (fun y : nat => j = (j+y)) 0 (eq_sym (Zria j))
                | i,0       =>  exist (eq (max i 0)) (max i 0) eq_refl
                | S i,S j   =>  let (y,q) := (k_frnt i j) in (exist (fun x : nat => (S (max i j)) = (S (j+x))) y (feq S q))
            end.

    (* relevant proofs- uniqueness of results, coincidence of results when applied to same argument twice *)
        Definition h_frnt_unique    : forall m n k : nat, (max m n) = (m+k) -> k = (proj1_sig (h_frnt m n))
            :=  nat_ind (fun m : nat => forall n k : nat, (max m n) = (m+k) -> k = (proj1_sig (h_frnt m n)))
                        (eq_sym (A:=nat))
                        (fun (i : nat) (IHi : forall j k : nat, (max i j) = (i+k) -> k = (proj1_sig (h_frnt i j))) (n k : nat) =>
                         match n as j return ((max (S i) j) = (S (i+k)) -> k = (proj1_sig (h_frnt (S i) j))) with
                            | 0     =>  fun e : (S i) = (S (i+k)) =>
                                        (match i as x
                                         return (((max x 0) = (x+k) -> k = (proj1_sig (h_frnt x 0))) -> x = (x+k) -> k = 0)
                                         with 0 => id | S x => id end) (IHi 0 k) (feq pred e)
                            | S j   =>  fun e : (S (max i j)) = (S (i+k)) =>
                                        eq_trans    (IHi j k (feq pred e))
                                                    (let (x,_) as s
                                                     return ((proj1_sig s)
                                                                = (proj1_sig (let (x,p) := s in
                                                                                exist   (fun y : nat => (S (max i j)) = (S (i+y)))
                                                                                        x (feq S p))))
                                                        := (h_frnt i j) in eq_refl)
                         end).
        Definition k_frnt_unique    : forall m n k : nat, (max m n) = (n+k) -> k = (proj1_sig (k_frnt m n))
            :=  nat_ind (fun m : nat => forall n k : nat, (max m n) = (n+k) -> k = (proj1_sig (k_frnt m n)))
                        (nat_ind    (fun n : nat => forall k : nat, n = (n+k) -> k = 0) (eq_sym (x:=0))
                                    (fun (j : nat) (f : forall k : nat, j = (j+k) -> k = 0) (k : nat) (e : (S j) = (S (j+k))) =>
                                     f k (feq pred e)))
                        (fun (i : nat) (f : forall j k : nat, (max i j) = (j+k) -> k = (proj1_sig (k_frnt i j))) (n k : nat) =>
                         match n as j return ((max (S i) j) = (j+k) -> k = (proj1_sig (k_frnt (S i) j))) with
                            | 0     =>  @eq_sym nat (S i) k
                            | S j   =>  fun e : (S (max i j)) = (S (j+k)) =>
                                        eq_trans    (f j k (feq pred e))
                                                    (let (x,_) as s
                                                     return ((proj1_sig s)
                                                                = (proj1_sig (let (y,q) := s in
                                                                                exist   (fun x : nat => (S (max i j)) = (S (j+x)))
                                                                                        y (feq S q))))
                                                        := (k_frnt i j) in eq_refl)
                         end).
        Definition frnts_idem       : forall m : nat, (h_frnt m m) = (k_frnt m m)
            :=  nat_ind (fun m : nat => (h_frnt m m) = (k_frnt m m)) eq_refl
                        (fun i : nat =>
                         feq (fun s : {x : nat | (max i i) = (i+x)} =>
                              let (x,p) := s in exist (fun y : nat => (S (max i i)) = (S (i+y))) x (feq S p))).

(* DyCG.v- types *)
    (* remember: new type names (gotta make changes)
        kon will now be called xon
        update will now be called kon *)

    Notation "'e^' n" := (Vect e n) (at level 0) : vect_scope.
    Definition con : nat -> Set := fun n : nat => e^n -> prop.
    (* kon will now be defined less generally- no quantification over "other" DR's; gonna outsource that generalization to kext *)
    Definition kon : nat -> nat -> Set := fun m i : nat => con m -> con (m+i).
    (* mostly for reasons of comparing with the older setups, I'm gonna ressurect the type of "updates" for the old kon *)
    Definition update : nat -> nat -> Set := fun m i : nat => forall n : nat, kon (m+n) i.

    Fixpoint p_i (n : nat) {struct n} : Set := match n with 0 => prop | S i => e -> p_i i end.

    Definition udy' : (nat -> nat) -> nat -> nat -> Set
        := fun (f : nat -> nat) (n i : nat) => forall u : Vect nat n, kon (f (vmax u)) i.
    Definition udy  : nat -> nat -> nat -> Set := udy'∘max.

    Fixpoint dy' (f : nat -> nat) (n i : nat) {struct n} : Set
        :=  match n with
                | 0     => kon (f 0) i
                | S j   => forall m : nat, dy' (f∘(max (S m))) j i
            end.
    Definition dy : nat -> nat -> nat -> Set := dy'∘max.

(* DyCG.v- basics *)
    (*  casts are basically just eq_rec with equated nat's implicit- see comments below each for converting them
        into versions where the arguments are the ones that get casted *)
    Definition ccast : forall {m : nat}, con m -> forall {n : nat}, m = n -> con n
        := fun m : nat => eq_rec m con.
        (* := fun (m : nat) (c : con m) (n : nat) (d : m = n) (v : e^n) => c (vcast v (eq_sym d)). *)
    Definition kcast : forall {m i : nat}, kon m i -> forall {n : nat}, m = n -> kon n i
        := fun m i : nat => eq_rec m (flip kon i).
        (* :=  fun (m i : nat) (k : kon m i) (n : nat) (d : m = n) (c : con n) (v : e^(n+i)) =>
            k (ccast c (eq_sym d)) (vcast v (eq_sym (feq (flip plus i) d))). *)

    (* cext,kext *)
    (* context extension- defined to add arbitrary # of DR's, but the c⁺ notation will still be for +1 *)
    Definition cext : forall i : nat, update 0 i := fun (i n : nat) (c : con n) (v : e^(n+i)) => c (take n v).
    Notation "c ⁺" := (cext 1 _ c) (at level 0) : dyn_scope.
    Open Scope dyn_scope.
    Definition kext : forall {m i : nat}, kon m i -> update m i
        :=  fun (m i : nat) (k : kon m i) (n : nat) (c : con (m+n)) (v : e^((m+n)+i)) =>
            (* v ≈ ((l ++ u) ++ r) *)
            let l := (take m (take (m+n) v)) in
            let u := (drop m (take (m+n) v)) in
            let r := (drop (m+n) v) in
            k (fun t : e^m => c (t ++ u)) (l ++ r).
        (* definition is such that the context sees the n "extra" DR's, but k itself never interacts with them directly *)
        (* this may lead to weirdness in the indexing of DR's, but then again so has everything else so far *)

    Definition dy1ext'  : forall (f : nat -> nat) (n i : nat), dy' f 1 i -> dy' ((max n)∘f) 1 i
        :=  fun (f : nat -> nat) (n i : nat) (D : dy' f 1 i) (m : nat) =>
            let (y,q) := (k_frnt n (f (S m))) in kcast (kext (D m) y) (eq_sym q).

    Definition dy1ext   : forall {m i : nat}, dy m 1 i -> forall n : nat, dy (max m n) 1 i
        :=  fun (m i : nat) (D : dy m 1 i) (n j : nat) =>
            let (y,q) := (k_frnt n (max m (S j))) in
            kcast (kext (D j) y) (eq_trans' q (eq_trans' (max_assoc n m (S j)) (feq (flip max (S j)) (max_comm n m)))).

    (* Definition d1ext: forall {m i : nat}, dy m 1 i -> forall n : nat, dy (m+n) 1 i. *)
    (* shouldn't I be able to do this with a variant of dy1ext since (max m (m+n)) = (m+n)? *)

    Fixpoint vexists {n : nat} : con n -> prop
        :=  match n as k return (con k -> prop) with
                | 0     =>  fun c : con 0 => c []
                | S i   =>  fun c : con (S i) => pex (fun x : e => vexists (fun v : e^i => c (x::v)))
            end.

    Definition cc : forall {m i : nat}, kon m i -> kon m i
        := fun (m i : nat) (k : kon m i) (c : con m) (v : e^(m+i)) => (c (take m v)) and (k c v).

    (* order or kext-ing and recasting kon's doesn't change anything *)
    Definition kextkcast    : forall {m n i : nat} (k : kon m i) {j : nat} (d : m = j) (c : con (j+n)) (v : e^((j+n)+i)),
        (kcast (kext k n) (feq (flip plus n) d) c v) = (kext (kcast k d) n c v)
        :=  fun (m n i : nat) (k : kon m i) =>
            eq_ind_dep m
                (fun (j : nat) (d : m = j) => forall (c : con (j+n)) (v : e^((j+n)+i)),
                    (kcast (kext k n) (feq (flip plus n) d) c v) = (kext (kcast k d) n c v))
                (fun (c : con (m+n)) (v : e^((m+n)+i)) => eq_refl).
    (* don't actually need to quantify over contexts and DR vectors! *)
    Definition kextkcastfun : forall {m n i : nat} (k : kon m i) {j : nat} (d : m = j),
        (kcast (kext k n) (feq (flip plus n) d)) = (kext (kcast k d) n)
        :=  fun (m n i : nat) (k : kon m i) =>
            eq_ind_dep m (fun (j : nat) (d : m = j) => (kcast (kext k n) (feq (flip plus n) d)) = (kext (kcast k d) n)) eq_refl.
    (* can avoid quantifying over k as well! *)
    Definition kextkcastfun2 : forall {m n i j : nat} (d : m = j),
        (fun k : kon m i => kcast (kext k n) (feq (flip plus n) d)) = (fun k : kon m i => kext (kcast k d) n)
        :=  fun m n i : nat =>
            eq_ind_dep m
                (fun (j : nat) (d : m = j) =>
                    (fun k : kon m i => kcast (kext k n) (feq (flip plus n) d)) = (fun k : kon m i => kext (kcast k d) n))
                eq_refl.
    (* can even avoid quantifying over i and n! *)
    Definition kextkcastfun3 : forall {m j : nat} (d : m = j),
        (fun (i : nat) (k : kon m i) (n : nat) => kcast (kext k n) (feq (flip plus n) d))
            = (fun (i : nat) (k : kon m i) => kext (kcast k d))
        :=  fun m : nat =>
            eq_ind_dep m
                (fun (j : nat) (d : m = j) =>
                    (fun (i : nat) (k : kon m i) (n : nat) => kcast (kext k n) (feq (flip plus n) d))
                    = (fun (i : nat) (k : kon m i) => kext (kcast k d)))
                eq_refl.

    (* order of performing cc/kext on a content doesn't change anything *)
    Definition kextcc : forall {m n i:nat}(k:kon m i)(c:con (m+n))(v:e^((m+n)+i)), (cc (kext k n) c v) = (kext (cc k) n c v)
        :=  fun (m n i : nat) (k : kon m i) (c : con (m+n)) (v : e^((m+n)+i)) =>
            let l := (take (m+n) v) in
            let r := (drop (m+n) v) in
            feq (fun u : e^(m+n) => (c u) and (k (fun t : e^m => c (t ++ (drop m l))) ((take m l) ++ r)))
                (eq_trans (tkdr_app_inv m l) (feq (fun u : e^m => u ++ (drop m l)) (tkdr_app_inv2a m (take m l) r))).
    (* maybe do a similar proof for kext vs AND,etc? *)

(* DyCG.v- "propositional" level *)
    Definition NOT : forall {m i : nat}, kon m i -> kon m 0
        :=  fun (m i : nat) (k : kon m i) (c : con m) (v : e^(m+0)) =>
            not (vexists (fun u : e^i => k c ((take m v) ++ u))).

    Definition dynNOT : forall {m i : nat} (k : kon m i) (c : con m) (v : e^m),
        (NOT (NOT k) c (v ++ [])) ≡ (vexists (fun u : e^i => k c (v ++ u)))
        :=  fun (m i : nat) (k : kon m i) (c : con m) (v : e^m) =>
            let C := (fun l : e^m => vexists (fun u : e^i => k c (l ++ u))) in
            let V := (fun (n : nat) (l : e^n) => take n ((take n (l ++ [])) ++ [])) in
            int_eq  (NOT (NOT k) c (v ++ [])) (C v)
                    (fun w : world =>
                         eq_trans   (p_not_ax (not (C (V m v))) w)
                        (eq_trans   (f_equal negb (p_not_ax (C (V m v)) w))
                        (eq_trans   (if ((C (V m v))@w) as b return (-~(-~b) = b) then eq_refl else eq_refl)
                                    (f_equal    (fun l : e^m => (C l)@w)
                                                (Vect_ind e (fun (n : nat) (l : e^n) => (V n l) = l) eq_refl
                                                            (fun (j : nat) (x : e) (l : e^j) => feq (vcons x)) m v))))).

    Definition kextNOT : forall {m n i:nat}(k:kon m i)(c:con (m+n))(v:e^(m+n)),(NOT(kext k n)c(v++[]))=(kext(NOT k)n c(v++[]))
        :=  fun (m n i : nat) (k : kon m i) (c : con (m+n)) (v : e^(m+n)) =>
            feq3    (fun (f : e^i -> e^(m+n)) (g : e^i -> e^m) (h : e^i -> e^i) =>
                        not (vexists (fun u : e^i => k (fun t : e^m => c (t ++ (drop m (f u)))) ((g u) ++ (h u)))))
                    (tkdr_app_inv3a (take (m+n) (v ++ [])))
                    (eq_trans   (feq    (comp (take m)) (tkdr_app_inv3a (take (m+n) (v ++ []))))
                                (feq    (fun (l : e^m) (_ : e^i) => l)
                                        (tkdr_app_inv2a m (take m (take (m+n) (v ++ []))) (drop (m+n) (v ++ [])))))
                    (tkdr_app_inv3b (take (m+n) (v ++ []))).

    Definition d_AND : forall {m i j : nat}, kon m i -> kon (m+i) j -> kon m (i+j)
        :=  fun (m i j : nat) (h : kon m i) (k : kon (m+i) j) (c : con m) (v : e^(m+(i+j))) =>
            let u := (vcast v (add_assoc m i j)) in (h c (take (m+i) u)) and (k (cc h c) u).
    Infix "AND" := d_AND (at level 20) : dyn_scope.

    (* 15 lines!!!! *)
    Definition dynAND : forall (m i j : nat) (h : kon m i) (k : kon (m+i) j) (c : con m) (v : e^(m+(i+j))),
        (cc (h AND k) c v) ≡ (cc k (cc h c) (vcast v (add_assoc m i j)))
        :=  fun (m i j : nat) (h : kon m i) (k : kon (m+i) j) (c : con m) (v : e^(m+(i+j))) =>
            let u := (vcast v (add_assoc m i j)) in
            let P := (c (take m v)) in
            let Q := (h c (take (m+i) u)) in
            let R := (k (cc h c) u) in
            let T := (c (take m (take (m+i) u))) in
            int_eq  (cc (h AND k) c v) (cc k (cc h c) u)
                    (fun w : world =>
                         eq_trans   (p_and_ax P ((h AND k) c v) w)
                        (eq_trans   (feq (andb (P@w)) (p_and_ax Q R w))
                        (eq_trans   (andb_assoc (P@w) (Q@w) (R@w))
                        (eq_trans   (feq (fun l : e^m => ((c l)@w && Q@w) && R@w) (take_assoc m i j v))
                        (eq_sym     (eq_trans (p_and_ax (T and Q) R w) (feq (flip andb (R@w)) (p_and_ax T Q w)))))))).

    Definition d_OR : forall {m i j : nat}, kon m i -> kon m j -> kon m 0
        := fun (m i j : nat) (h : kon m i) (k : kon m j) => NOT ((NOT h) AND (NOT (kext k 0))).
    Infix "OR" := d_OR (at level 0) : dyn_scope.

    Definition d_IMPLIES : forall {m i j : nat}, kon m i -> kon (m+i) j -> kon m 0
        := fun (m i j : nat) (h : kon m i) (k : kon (m+i) j) => (NOT h) OR (h AND k).
    Infix "IMPLIES" := d_IMPLIES (at level 20) : dyn_scope.

(* DyCG.v- predicate level *)
    (* the use of kext in here is…interesting, to say the least. Wonder what it'll mean for the indices later? *)
    Fixpoint udyn (m : nat) {struct m} : p_i m -> udy 0 m 0
        :=  match m as k return (p_i k -> udy 0 k 0) with
                | 0     =>  fun (p : prop) (_ : Vect nat 0) (_ : con 0) (_ : e^0) => p
                | S i   =>  fun (P : e -> p_i i) (u : Vect nat (S i)) (c : con (vmax u)) (v : e^((vmax u)+0)) =>
                            let (x,p) := (h_frnt (S (head u)) (vmax (tail u))) in
                            let (y,q) := (k_frnt (S (head u)) (vmax (tail u))) in
                            kext    (udyn i (P (nth (head u) (vcast v (eq_trans (Zria (vmax u)) p)))) (tail u))
                                    y (ccast c q) (vcast v (feq (flip plus 0) q))
            end.

    Fixpoint udytody (f : nat -> nat) (n i : nat) {struct n} : udy' f n i -> dy' f n i
      :=    match n as j return (udy' f j i -> dy' f j i) with
                | 0     =>  fun g : Vect nat 0 -> kon (f 0) i => g []
                | S j   =>  fun (g : forall u : Vect nat (S j), kon (f (vmax u)) i) (m : nat) =>
                            udytody (f∘(max (S m))) j i (fun r : Vect nat j => g (m::r))
            end.

    Definition dyn  : forall n : nat, p_i n -> dy  0 n 0 := fun (n : nat) (P : p_i n) => udytody id n 0 (udyn n P).

    (* New! 11/18/2018: converting back from dy' to udy', plus proof that they form an iso (up to functional extensionality of index arg's) *)
    Fixpoint dytoudy (f : nat -> nat) (k i : nat) {struct k} : dy' f k i -> udy' f k i
        :=  match k as n return (dy' f n i -> udy' f n i) with
                | 0     =>  fun (h : dy' f    0  i) (_ : Vect nat    0 ) => h
                | S j   =>  fun (D : dy' f (S j) i) (u : Vect nat (S j)) =>
                            eq_rec ((head u)::(tail u)) (fun v : Vect nat (S j) => xon (f (vmax v)) i) (dytoudy (f∘(max (S (head u)))) j i (D (head u)) (tail u)) u (Vect_form u)
            end.

    Definition udu_inv : forall (i k : nat) (u : Vect nat k) (f : nat -> nat) (D : udy' f k i), (dytoudy f k i (udytody f k i D) u) = (D u)
        :=  fun i : nat =>
            Vect_ind nat    (fun (k : nat) (u : Vect nat k) => forall (f : nat -> nat) (D : udy' f k i), (dytoudy f k i (udytody f k i D) u) = (D u))
                            (fun (f : nat -> nat) (D : udy' f 0 i) => eq_refl)
                            (fun (k n : nat) (r : Vect nat k) (g : forall (h : nat -> nat) (E : udy' f k i), (dytoudy h k i (udytody h k i E) r) = (E r))
                                 (f : nat -> nat) (D : udy' f (S k) i) => g (f∘(max (S n))) (fun t : Vect nat k => D (n::t))).

    Definition dud_type : forall (i k : nat) (f : nat -> nat), dy' f k i -> Prop
        :=  fun i : nat => nat_rect (fun k : nat => forall f : nat -> nat, dy' f k i -> Prop)
                                    (fun (f : nat -> nat) (h : xon (f 0) i) => (udytody f 0 i (dytoudy f 0 i h)) = h)
                                    (fun (k : nat) (P : forall g : nat -> nat, dy' g k i -> Prop) (f : nat -> nat) (D : dy' f (S k) i) => forall n : nat, P (f∘(max (S n))) (D n)).

    Definition dud_inv : forall (i k : nat) (f : nat -> nat) (D : dy' f k i), dud_type i k f D
        :=  fun i : nat =>
            nat_ind (fun k : nat => forall (f : nat -> nat) (D : dy' f k i), dud_type i k f D)
                    (fun (f : nat -> nat) (D : xon (f 0) i) => eq_refl)
                    (fun (k : nat) (h : forall (g : nat -> nat) (E : dy' g k i), dud_type i k g E) (f : nat -> nat) (D : dy' f (S k) i) (n : nat) => h (f∘(max (S n))) (D n)).


(* Dynamic Quantifiers *)
    Definition EXISTS : forall {m i : nat}, dy m 1 i -> kon m (S i)
        :=  fun (m i : nat) (D : dy m 1 i) (c : con m) (v : e^(m+(S i))) =>
            kcast (D m) (eq_trans (feq (max m) (add_comm 1 m)) (max_plus m 1)) c⁺ (vcast v (add_assoc m 1 i)).
    Definition FORALL : forall {m i : nat}, dy m 1 i -> kon m 0
        := fun (m i : nat) (D : dy m 1 i) => NOT (EXISTS (fun j : nat => NOT (D j))).

    (* type-correct version of THAT which feeds D and E different indices *)
    Definition bad_THAT : forall {m i j : nat}, dy m 1 i -> dy (m+i) 1 j -> dy m 1 (i+j)
        :=  fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) (n : nat) =>
            (D n) AND (kcast (E (n+i)) (max_k_plus m (S n) i)).
    Infix "bTHAT" := bad_THAT (at level 20) : dyn_scope.

    Definition badSOME  : forall {m i j : nat}, dy m 1 i -> dy (m+i) 1 j -> kon m (S (i+j))
        := fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) => EXISTS (D bTHAT E).

    Definition badEVERY : forall {m i j : nat}, dy m 1 i -> dy (m+i) 1 j -> kon m 0
        :=  fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) =>
            FORALL (fun n : nat => (D n) IMPLIES (kcast (E (n+i)) (max_k_plus m (S n) i))).

    Definition IT       : forall (n : nat) {m i : nat}, dy m 1 i -> kon (max m (S n)) i
        := fun (n m i : nat) (D : dy m 1 i) => D n.

(* attempt at "working" version of SOME *)
    (* Definition SOME'    : forall {m i j : nat}, dy m 1 i -> dy (m+i) 1 j -> kon m (S (i+j))
        :=  fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) (c : con m) (v : e^(m+(S (i+j)))) =>
            (kcast (D m) (eq_trans (max_succ m) (add_comm 1 m)))
            AND
            (kcast (kext (E m) (if i then 0 else 1)) (kindaspecprf m i))
            c⁺ (vcast v (add_assoc m 1 (i+j))). *)

    (* Definition pred : nat -> nat := fun m : nat => match m with 0 => 0 | S i => i end.
    Definition fooproofthingy : forall m i : nat, (max (m+i) (S m)) = (S (m+(pred i)))
        :=  fun m i : nat =>
            (fix nxt (x : nat) {struct x} : (max (x+i) (S x)) = (S (x+(pred i))) :=
             match x as y return ((max (y+i) (S y)) = (S (y+(pred i)))) with
                | 0     =>  max_comm i 1
                | S y   =>  feq S (nxt y)
             end) m.

    Definition kindaspecprf : forall m i : nat, ((max (m+i) (S m))+(if i then 0 else 1)) = ((m+1)+i)
        :=  fun m i : nat =>
            eq_trans    (feq (flip plus (if i then 0 else 1)) (eq_trans (feq (max (m+i)) (add_comm 1 m)) (max_add i 1 m)))
                        (eq_trans'  (add_assoc m (max i 1) (if i then 0 else 1))
                                    (eq_trans   (feq (plus m)
                                                    (match i as x
                                                     return (((max x 1)+(if x then 0 else 1)) = (S x)) with
                                                        | 0     => eq_refl
                                                        | S x   => feq S (eq_trans  (add_comm (max x 0) 1)
                                                                                    (feq S (Zrix x)))
                                                     end))
                                                (add_assoc m 1 i))). *)

(* Static term assumptions *)
    Axioms farmer donkey bray : e -> prop.
    Axioms own beat : e -> e -> prop.
    Axioms john bill chiquita : e.

(* Dynamic lexical item definitions *)
    Definition BRAY     : dy 0 1 0 := dyn 1 bray.
    Definition FARMER   : dy 0 1 0 := dyn 1 farmer.
    Definition DONKEY   : dy 0 1 0 := dyn 1 donkey.
    Definition OWN      : dy 0 2 0 := dyn 2 own.
    Definition BEAT     : dy 0 2 0 := dyn 2 beat.
    Definition OutBlue  : forall {n : nat}, con n := fun (n : nat) (_ : e^n) => truth.

(* old Back to testing sentences *)
    (* The second form of a donkey sentence- "if a farmer owns a donkey, he beats it" *)
        (* Definition IAFOADHBI : kon 0 0 := d_IMPLIES (n:=0) AFOAD (BEAT 0 1). *)
            (*  (IT 0 (fun m : nat => eq_rec (max m 1) ((flip kon 0)∘S) (IT 1 (BEAT m)) (max 1 m) (max_comm m 1))) : kon 2 0
                (IT 1 (fun n : nat =>
                            eq_rec  (max n 0) ((flip kon 0)∘S)
                                    (IT 0 (fun m : nat => eq_rec (max m n) ((flip kon 0)∘S) (BEAT m n) (max n m) (max_comm m n)))
                                    n (Zrix n))) : kon 2 0
                Both reduce to (BEAT 0 1) *)
            (* ≡ (fun (_ : con 0) (_ : e^0) =>
                    (some farmer (fun x : e => some donkey (own x)))
                        implies (some farmer (fun x : e => some (donkey that (own x)) (beat x)))) *)


(* newer testings- looking good so far, believe it or not! *)
    (* "Some donkey brayed" vs "There exists a donkey₀ and it₀ brayed" *)
        Definition exdonkandbr  : kon 0 1   := (EXISTS DONKEY) AND (IT 0 BRAY).
            (* :=: (fun (_ : con 0) (v : e^1) => let x := (nth 0 v) in (donkey x) and (bray x)) *)
            (* "There is a donkey₀ and it₀ brayed" *)
        Definition smdonkbr     : kon 0 1   := (badSOME DONKEY BRAY).
            (* :=: (fun (_ : con 0) (v : e^1) => let x := (nth 0 v) in (donkey x) and (bray x)) *)
            (* "Some donkey brayed" *)
    (* "A farmer owns a donkey", with both scopings of farmer vs donkey *)
        Definition AFOAD1       : kon 0 2   := badSOME FARMER (fun m : nat => badSOME (dy1ext DONKEY (S m)) (OWN (m+0))).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in (farmer x) and ((donkey y) and (own x y))) *)
            (* "A farmer₀ owns a donkey₁", farmer>donkey *)
        Definition AFOAD2       : kon 0 2
            :=  badSOME DONKEY
                        (fun n : nat =>
                         badSOME    (dy1ext FARMER (S n))
                                    (fun m : nat => kcast (OWN m (n+0)) (max_comm (S m) (S (n+0))))).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in (donkey x) and ((farmer y) and (own y x))) *)
            (* "A farmer₁ owns a donkey₀", donkey>farmer *)
    (* "A farmer owns a donkey. It brays" with both scopings *)
        Definition FODDBR1      : kon 0 2   := AFOAD1 AND (IT 1 BRAY).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                        ((farmer x) and ((donkey y) and (own x y))) and (bray y)) *)
            (* "A farmer₀ owns a donkey₁. It₁ brays." *)
        Definition FODDBR2      : kon 0 2   := AFOAD2 AND (kext (IT 0 BRAY) 1).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                    ((donkey x) and ((farmer y) and (own y x))) and (bray x)) *)
            (* "A farmer₁ owns a donkey₀. It₀ brays." *)
    (* "A farmer owns a donkey. He brays" with both scopings *)
        Definition FODFBR1      : kon 0 2   := AFOAD1 AND (kext (IT 0 BRAY) 1).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                    ((farmer x) and ((donkey y) and (own x y))) and (bray x)) *)
            (* "A farmer₀ owns a donkey₁. He₀ brays." *)
        Definition FODFBR2      : kon 0 2   := AFOAD2 AND (IT 1 BRAY).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                    ((donkey x) and ((farmer y) and (own y x))) and (bray y)) *)
            (* "A farmer₁ owns a donkey₀. He₁ brays." *)

    (* "A farmer owns a donkey that brays" *)
    Definition FODB     : kon 0 2
        := badSOME FARMER (fun m : nat => badSOME ((dy1ext DONKEY (S m)) bTHAT (OWN (m+0))) (dy1ext BRAY (S (m+0)))).
        (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                    (farmer x) and (((donkey y) and (own x y)) and (bray y))) *)

    (* "A farmer owns a donkey that brays. He brays (too)." *)
    Definition FODBFB   : kon 0 2 := FODB AND (kext (IT 0 BRAY) 1).
        (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                    ((farmer x) and (((donkey y) and (own x y)) and (bray y))) and (bray x)) *)

    (* "A farmer owns a donkey that brays. It also brays." *)
    Definition FODBDB   : kon 0 2 := FODB AND (IT 1 BRAY).
        (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                    ((farmer x) and (((donkey y) and (own x y)) and (bray y))) and (bray y)) *)


(*  some simpler problem cases- anaphoric reference outside of the sentence works correctly,
    but fails within the scope of the quantifier in the sentence itself (almost as if it was being passed a bad argument…
    (/sarcasm)) *)

    (* "A farmer who owns a donkey brays"- predicts that the donkey is the braying one *)
        Definition AFOADB   : kon 0 2
            := badSOME (FARMER bTHAT (fun m : nat => badSOME (dy1ext DONKEY (S m)) (OWN (m+0)))) (dy1ext BRAY 1).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                    ((farmer x) and ((donkey y) and (own x y))) and (bray y)) *)
        (* "A farmer who owns a donkey brays. It brays (too)." *)
        Definition AFOADRDB : kon 0 2 := AFOADB AND (IT 1 BRAY).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                        (((farmer x) and ((donkey y) and (own x y))) and (bray y)) and (bray y)) *)
        (* "A farmer who owns a donkey brays. He also brays." *)
        Definition AFOADBFB : kon 0 2 := AFOADB AND (kext (IT 0 BRAY) 1).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                        (((farmer x) and ((donkey y) and (own x y))) and (bray y)) and (bray x)) *)
    (* "A donkey that some farmer owns brays"- predicts the farmer is the braying one *)
        Definition ADSFOB   : kon 0 2
            :=  badSOME (DONKEY bTHAT
                            (fun n : nat =>
                                badSOME (dy1ext FARMER (S n)) (fun m : nat => kcast (OWN m (n+0)) (feq S (max_comm m (n+0))))))
                        (dy1ext BRAY 1).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                        ((donkey x) and ((farmer y) and (own y x))) and (bray y)) *)
        (* "A donkey that some farmer owns brays. It also brays." *)
        Definition ADSFOBDB   : kon 0 2 := ADSFOB AND (kext (IT 0 BRAY) 1).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                        (((donkey x) and ((farmer y) and (own y x))) and (bray y)) and (bray x)) *)
        (* "A donkey that some farmer owns brays. He brays (too)." *)
        Definition ADSFOBFB   : kon 0 2 := ADSFOB AND (IT 1 BRAY).
            (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                        (((donkey x) and ((farmer y) and (own y x))) and (bray y)) and (bray y)) *)


(* dare I try…the donkey sentence? *)
(* still failed… *)
Definition the_donkey_sentence : kon 0 0
    :=  badEVERY    (FARMER bTHAT (fun m : nat => badSOME (dy1ext DONKEY (S m)) (OWN (m+0))))
                    (fun m : nat => kcast (IT 0 (BEAT m)) (feq S (Zrix m))).

    (* :=: (fun (_ : con 0) (_ : e^0) =>
         not (pex (fun x : e =>
                    not (not ((not (not (pex (fun y : e => farmer x and ((donkey y) and (own x y))))))
                                and (not (pex (fun y : e => ((farmer x) and ((donkey y) and (own x y))) and (beat y x)))))))))
    :≡: (fun (_ : con 0) (_ : e^0) =>
         every  (fun x : e => (farmer x) and (some donkey (own x)))
                (fun x : e => (farmer x) and (some (donkey that (own x)) (flip beat x)))) *)


(* maybe the issue is the picking of the new DR as the first of the "new" DR's? idk *)
(*  anyway, problem shows up pretty early- especially worrisome to me (other than the THAT situation)
    is that IT pretty much needs to select the 0th element, yet this points to the wrong DR, right? *)
(* the_donkey_sentence : kon 0 0
    :=: (badEVERY   (FARMER THAT (fun m : nat => badSOME (dy1ext DONKEY (S m)) (OWN (m+0))))
                    (fun m : nat => kcast (IT 0 (BEAT m)) (feq S (Zrix m))))
    :=: (@badEVERY 0 1 0
            (@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))))
            (fun m : nat => kcast (IT 0 (BEAT m)) (feq S (Zrix m))))
    :=: (FORALL (fun m : nat =>
                    (@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))) m)
                        IMPLIES (kcast (kcast (IT 0 (BEAT (m+1))) (feq S (Zrix (m+1)))) (max_k_plus 0 (S m) 1))))
    :=: (@FORALL 0 0
                (fun m : nat =>
                    (@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))) m)
                        IMPLIES (kcast (kcast (IT 0 (BEAT (m+1))) (feq S (Zrix (m+1)))) (max_k_plus 0 (S m) 1))))
    :=: (NOT (EXISTS
                (fun m : nat =>
                 NOT ((@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))) m)
                        IMPLIES (kcast (kcast (IT 0 (BEAT (m+1))) (feq S (Zrix (m+1)))) (max_k_plus 0 (S m) 1))))))
    :=: (@NOT 0 1
            (EXISTS
                (fun m : nat =>
                 NOT ((@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))) m)
                        IMPLIES (kcast (kcast (IT 0 (BEAT (m+1))) (feq S (Zrix (m+1)))) (max_k_plus 0 (S m) 1))))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                 EXISTS
                    (fun m : nat =>
                     NOT ((@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))) m)
                            IMPLIES (kcast (kcast (IT 0 (BEAT (m+1))) (feq S (Zrix (m+1)))) (max_k_plus 0 (S m) 1))))
                    c [x])))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                 @EXISTS 0 0
                    (fun m : nat =>
                     NOT ((@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))) m)
                            IMPLIES (kcast (kcast (IT 0 (BEAT (m+1))) (feq S (Zrix (m+1)))) (max_k_plus 0 (S m) 1))))
                    c [x])))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                     NOT ((@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))) 0)
                            IMPLIES (IT 0 (BEAT 1))) c⁺ [x])))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                     @NOT 1 0
                        ((@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))) 0)
                            IMPLIES (IT 0 (BEAT 1)))
                        c⁺ [x])))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not ((@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))) 0)
                                IMPLIES (IT 0 (BEAT 1)) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (@bad_THAT 0 0 1 FARMER (fun m : nat => @badSOME (S m) 0 0 (dy1ext DONKEY (S m)) (OWN (m+0))) 0)
                                (IT 0 (BEAT 1)) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0   ((FARMER 0) AND (@badSOME 1 0 0 (dy1ext DONKEY 1) (OWN 0)))
                                                (IT 0 (BEAT 1)) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (@d_AND 1 0 1 (FARMER 0) (@badSOME 1 0 0 (dy1ext DONKEY 1) (OWN 0)))
                                (@IT 0 2 0 (BEAT 1)) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (FARMER 0 d [head v]) and (@badSOME 1 0 0 (dy1ext DONKEY 1) (OWN 0) (cc (FARMER 0) d) v))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v)) and (EXISTS ((dy1ext DONKEY 1) THAT (OWN 0)) (cc (FARMER 0) d) v))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v))
                                        and (@EXISTS 1 0 (@bad_THAT 1 0 0 (dy1ext DONKEY 1) (OWN 0)) (cc (FARMER 0) d) v))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v)) and (@bad_THAT 1 0 0 (dy1ext DONKEY 1) (OWN 0) 1 (cc (FARMER 0) d)⁺ v))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v)) and ((dy1ext DONKEY 1 1) AND (OWN 0 1) (cc (FARMER 0) d)⁺ v))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v)) and (@d_AND 2 0 0 (dy1ext DONKEY 1 1) (OWN 0 1) (cc (FARMER 0) d)⁺ v))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v))
                                        and ((dy1ext DONKEY 1 1 (cc (FARMER 0) d)⁺ (take 2 v))
                                                and (OWN 0 1 (cc (dy1ext DONKEY 1 1) (cc (FARMER 0) d)⁺) v)))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v))
                                        and ((@dy1ext 0 0 DONKEY 1 1 (cc (FARMER 0) d)⁺ (take 2 v))
                                                and (OWN 0 1 (cc (dy1ext DONKEY 1 1) (cc (FARMER 0) d)⁺) v)))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v))
                                        and ((kext (DONKEY 1) 0 (cc (FARMER 0) d)⁺ (take 2 v))
                                                and (OWN 0 1 (cc (dy1ext DONKEY 1 1) (cc (FARMER 0) d)⁺) v)))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v))
                                        and ((@kext 2 0 (DONKEY 1) 0 (cc (FARMER 0) d)⁺ (take 2 v))
                                                and (OWN 0 1 (cc (dy1ext DONKEY 1 1) (cc (FARMER 0) d)⁺) v)))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v))
                                        and ((DONKEY 1 (fun t : e^2 => (cc (FARMER 0) d)⁺ (t ++ [])) [head v,head (tail v)])
                                                and (OWN 0 1 (cc (dy1ext DONKEY 1 1) (cc (FARMER 0) d)⁺) v)))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_IMPLIES 1 1 0
                                (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v)) and ((donkey (head (tail v))) and (own (head v) (head (tail v)))))
                                (BEAT 1 0) c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not ((NOT (fun (d : con 1) (v : e^2) =>
                                    (farmer (head v)) and ((donkey (head (tail v))) and (own (head v) (head (tail v))))))
                                OR ((fun (d : con 1) (v : e^2) =>
                                        (farmer (head v)) and ((donkey (head (tail v))) and (own (head v) (head (tail v)))))
                                        AND (BEAT 1 0))
                                c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@d_OR 1 0 1
                                (NOT (fun (d : con 1) (v : e^2) =>
                                        (farmer (head v)) and ((donkey (head (tail v))) and (own (head v) (head (tail v))))))
                                ((fun (d : con 1) (v : e^2) =>
                                        (farmer (head v)) and ((donkey (head (tail v))) and (own (head v) (head (tail v)))))
                                        AND (BEAT 1 0))
                                c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (NOT ((NOT (NOT (fun (d : con 1) (v : e^2) =>
                                                (farmer (head v))
                                                    and ((donkey (head (tail v))) and (own (head v) (head (tail v)))))))
                                    AND (NOT (kext ((fun (d : con 1) (v : e^2) =>
                                                        (farmer (head v))
                                                            and ((donkey (head (tail v))) and (own (head v) (head (tail v)))))
                                         AND (BEAT 1 0)) 0)))
                                c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (@NOT 1 0
                                (@d_AND 1 0 0
                                    (@NOT 1 0 (@NOT 1 1
                                        (fun (d : con 1) (v : e^2) => (farmer (head v))
                                            and ((donkey (head (tail v))) and (own (head v) (head (tail v)))))))
                                    (@NOT 1 1 (kext
                                        ((fun (d : con 1) (v : e^2) => (farmer (head v))
                                            and ((donkey (head (tail v))) and (own (head v) (head (tail v)))))
                                        AND (BEAT 1 0)) 0)))
                                c⁺ [x]))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (not ((not (not (pex (fun y : e => (farmer x) and ((donkey y) and (own x y))))))
                                    and
                                    (not
                                     (pex
                                      (fun y : e =>
                                       kext ((fun (d : con 1) (v : e^2) => (farmer (head v))
                                                and ((donkey (head (tail v))) and (own (head v) (head (tail v)))))
                                                AND (BEAT 1 0))
                                                0 (cc (fun (d : con 1) (v : e^1) =>
                                                        not (not (pex
                                                                (fun y : e =>
                                                                    (farmer (head v)) and ((donkey y) and (own (head v) y)))))) c⁺)
                                                [x,y]))))))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (not ((not (not (pex (fun y : e => (farmer x) and ((donkey y) and (own x y))))))
                                    and
                                    (not
                                     (pex
                                      (fun y : e =>
                                       @kext 1 1 (@d_AND 1 1 0 (fun (d : con 1) (v : e^2) => (farmer (head v))
                                                and ((donkey (head (tail v))) and (own (head v) (head (tail v)))))
                                                (BEAT 1 0))
                                                0
                                                (cc (fun (d : con 1) (v : e^1) =>
                                                        not (not (pex
                                                                (fun y : e =>
                                                                    (farmer (head v)) and ((donkey y) and (own (head v) y)))))) c⁺)
                                                [x,y]))))))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (not ((not (not (pex (fun y : e => (farmer x) and ((donkey y) and (own x y))))))
                                    and (not (pex (fun y : e => ((farmer x) and ((donkey y) and (own x y)))
                                                        and (BEAT 1 0
                                                                (cc (fun (d : con 1) (v : e^2) => (farmer (head v)) and
                                                                        ((donkey (head (tail v)))
                                                                            and (own (head v) (head (tail v)))))
                                                                    (fun t : e^1 => cc (fun (d : con 1) (v : e^1) =>
                                                                                            not (not (pex (fun y : e =>
                                                                                                 (farmer (head v)) and
                                                                                                    ((donkey y)
                                                                                                        and (own (head v) y))))))
                                                                                        c⁺ (t ++ [])))
                                                                [x,y])))))))))
    :=: (fun (c : con 0) (_ : e^0) =>
            not (pex (fun x : e =>
                        not (not ((not (not (pex (fun y : e => (farmer x) and ((donkey y) and (own x y))))))
                                    and (not (pex (fun y : e => ((farmer x) and ((donkey y) and (own x y)))
                                                                    and (beat y x))))))))) *)


(* newer versions of the quantifier stuff, along with a new function- that_proof *)
    Fixpoint that_proof (m n i : nat) {struct n} : {k : nat | ((max (m+i) n)+k) = ((max m n)+i)}
        :=  match n as y return {k : nat | ((max (m+i) y)+k) = ((max m y)+i)} with
                | 0     =>  exist   (fun k : nat => ((max (m+i) 0)+k) = ((max m 0)+i)) 0
                                    (eq_trans (Zria (max (m+i) 0)) (eq_trans (Zrix (m+i)) (eq_sym (feq (flip plus i) (Zrix m)))))
                | S y   =>  match i as z return {k : nat | ((max (m+z) (S y))+k) = ((max m (S y))+z)} with
                                | 0     =>  exist   (fun k : nat => ((max (m+0) (S y))+k) = ((max m (S y))+0)) 0
                                                    (eq_trans   (Zria (max (m+0) (S y)))
                                                                (eq_trans   (feq (flip max (S y)) (Zria m))
                                                                            (eq_sym (Zria (max m (S y))))))
                                | S z   =>  match m as x return {k : nat | ((max (x+(S z)) (S y))+k) = ((max x (S y))+(S z))} with
                                                | 0     =>  let (a,p) := (that_proof 0 y z) in
                                                            exist   (fun k : nat => (S ((max z y)+k)) = (S (y+(S z)))) (S a)
                                                                    (feq S (eq_trans'   (Sdistr (max z y) a)
                                                                                        (eq_trans (feq S p) (Sdistr y z))))
                                                | S x   =>  let (b,q) := (that_proof x y (S z)) in
                                                            exist   (fun k : nat =>
                                                                        (S ((max (x+(S z)) y)+k)) = (S ((max x y)+(S z))))
                                                                    b (feq S q)
                                            end
                            end
            end.

    Definition d_THAT : forall {m i j : nat}, dy m 1 i -> dy (m+i) 1 j -> dy m 1 (i+j)
        :=  fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) (n : nat) =>
            let (k,p) := (that_proof m (S n) i) in (D n) AND (kcast (kext (E n) k) p).
    Infix "THAT" := d_THAT (at level 30) : dyn_scope.
    Definition SOME  : forall {m i j : nat}, dy m 1 i -> dy (m+i) 1 j -> kon m (S (i+j))
        := fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) => EXISTS (D THAT E).
    Definition EVERY : forall {m i j : nat}, dy m 1 i -> dy (m+i) 1 j -> kon m 0
        :=  fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) =>
            FORALL (fun n : nat => let (k,p) := (that_proof m (S n) i) in (D n) IMPLIES (kcast (kext (E n) k) p)).

(* not using that_proof, but does require additional functions, including subtraction and min *)
    Fixpoint min (m n : nat) {struct m} : nat := match m with 0 => 0 | S i => match n with 0 => 0 | S j => S (min i j) end end.
    Definition pred : nat -> nat := fun m : nat => match m with 0 => 0 | S i => i end.
    Definition Zramn : forall m : nat, (min m 0) = 0
        := fun m : nat => match m as i return ((min i 0) = 0) with 0 => eq_refl | S i => eq_refl end.
    Fixpoint minus (m n : nat) {struct m} : nat
        := match m with 0 => 0 | S i => match n with 0 => S i | S j => minus i j end end.
    Infix "-" := minus : type_scope. (* weirdness concerning the notation evaluations *)
    Definition Zris : forall m : nat, (m-0) = m
        := fun m : nat => match m as i return ((i-0) = i) with 0 => eq_refl | S i => eq_refl end.
    Fixpoint thtprf (m n i : nat) : ((max (m+i) n)+(min (n-m) i)) = ((max m n)+i)
        :=  match m as x,n as y,i as z return (((max (x+z) y)+(min (y-x) z)) = ((max x y)+z)) with
                | 0,0,z         =>  eq_trans (Zria (max z 0)) (Zrix z)
                | 0,S y,0       =>  eq_refl
                | 0,S y,S z     =>  feq S (eq_trans' (Sdistr (max z y) (min y z))
                                            (eq_trans   (feq S (eq_trans'
                                                                    (feq (fun a : nat => (max z y)+(min a z)) (Zris y))
                                                                    (thtprf 0 y z)))
                                                        (Sdistr y z)))
                | S x,0,z       =>  feq S (Zria (x+z))
                | S x,S y,z     =>  feq S (thtprf x y z)
            end.

    Definition d_THAT2 : forall {m i j : nat}, dy m 1 i -> dy (m+i) 1 j -> dy m 1 (i+j)
        :=  fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) (k : nat) =>
            let n := (min ((S k)-m) i) in
            (D k) AND (kcast (kext (E k) n) (thtprf m (S k) i)).
            (* @d_AND (max m (S k)) i j (D k)
                (@kcast ((max (m+i) (S k))+n) j (@kext (max (m+i) (S k)) j (E k) n) ((max m (S k))+i) (thtprf m (S k) i)). *)
    Infix "THAT2" := d_THAT2 (at level 30) : dyn_scope.
    Definition SOME2  : forall {m i j : nat}, dy m 1 i -> dy (m+i) 1 j -> kon m (S (i+j))
        := fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) => EXISTS (D THAT2 E).
    Definition EVERY2 : forall {m i j : nat}, dy m 1 i -> dy (m+i) 1 j -> kon m 0
        :=  fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) =>
            FORALL (fun n : nat => let k := (min ((S n)-m) i) in (D n) IMPLIES (kcast (kext (E n) k) (thtprf m (S n) i))).

(* new version of dynamic one-place predicate extension- makes use of minus *)
    Fixpoint d1exprf (m n j : nat) : ((max m j)+(n-(j-m))) = (max (m+n) j)
        :=  match m as x,n as y,j as z return (((max x z)+(y-(z-x))) = (max (x+y) z)) with
                | 0,0,z         =>  Zria z
                | 0,S y,0       =>  eq_refl
                | 0,S y,S z     =>  feq S (eq_trans' (feq (fun a : nat => z+(y-a)) (Zris z)) (d1exprf 0 y z))
                | S x,0,0       =>  eq_refl
                | S x,0,S z     =>  feq S (d1exprf x 0 z)
                | S x,S y,0     =>  eq_refl
                | S x,S y,S z   =>  feq S (d1exprf x (S y) z)
            end.

    Definition d1ext : forall {m i : nat}, dy m 1 i -> forall n : nat, dy (m+n) 1 i
        :=  fun (m i : nat) (D : dy m 1 i) (n k : nat) =>
            let j := (n-((S k)-m)) in kcast (kext (D k) j) (d1exprf m n (S k)).
            (* @kcast ((max m (S k))+j) i (@kext (max m (S k)) i (D k) j) (max (m+n) (S k)) (d1exprf m n (S k)). *)



(* testing newer version of the quantifiers with new THAT, but still dy1ext *)
    Definition the_donkey_sentence2 : kon 0 0
        :=  EVERY   (FARMER THAT (fun m : nat => SOME (dy1ext DONKEY (S m)) (OWN (m+0))))
                    (fun m : nat => kcast (IT 0 (BEAT m)) (feq S (Zrix m))).
        (* :=: (fun (_ : con 0) (_ : e^0) =>
             not (pex   (fun x : e =>
                         not (not ((not (not (pex (fun y : e => (farmer x) and ((donkey y) and (own x y))))))
                                    and (not (pex (fun y : e => ((farmer x) and ((donkey y) and (own x y)))
                                                    and (beat x x))))))))) *)
        (* :≡: (fun (_ : con 0) (_ : e^0) => every (fun x : e => (farmer x) and (some donkey (own x))) (fun x : e => beat x x)) *)

    Definition AFTOADBI : kon 0 2
        :=  SOME    (FARMER THAT (fun m : nat => SOME (dy1ext DONKEY (S m)) (OWN (m+0))))
                    (fun m : nat => kcast (IT 0 (BEAT m)) (feq S (Zrix m))).
        (* :=: (fun (_ : con 0) (v : e^2) => let (x,y) := (nth 0 v,nth 1 v) in
                ((farmer x) and ((donkey y) and (own x y))) and (beat x x)) *)


(* testing quantifiers with new THAT as well as d1ext instead of dy1ext *)
    Definition the_donkey_sentence3 : kon 0 0
        :=  @EVERY2 0 1 0
                    (@d_THAT2 0 0 1 FARMER
                        (fun m : nat => @SOME2 (S m) 0 0 (@d1ext 0 0 DONKEY (S m)) (OWN (m+0))))
                    (fun m : nat => @kcast (S (max m 0)) 0 (@IT 0 (S m) 0 (BEAT m)) (S m) (feq S (Zrix m))).
        (* yields same thing as old version… *)

    (* Definition AFTOADBI2 : kon 0 2 *)

