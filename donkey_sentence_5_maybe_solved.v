(* Probably missing some stuff from donkey_sentence_4.v, but hey- at least in this one I finally got the donkey sentence to come out correctly! *)
    (* missing stuff includes some of the proofs about the dynamic prop/predicate definitions *)

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
        :=  fun (A B C : Type) (f : A -> B -> C) (x a : A) (y b : B) => eq_ind x (fun z : A => y = b -> (f x y) = (f z b)) (feq (f x)) a.
    Definition feq3 : forall {A B C D : Type} (f : A -> B -> C -> D) {x a : A} {y b : B} {z c : C}, x = a -> y = b -> z = c -> (f x y z) = (f a b c)
            := fun (A B C D : Type) (f : A -> B -> C -> D) (x a : A) (y b : B) (z c : C) => eq_ind x (fun d : A => y = b -> z = c -> (f x y z) = (f d b c)) (feq2 (f x)) a.

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

    (* other defs *)
        Definition s_that   : (e -> prop) -> (e -> prop) -> e -> prop   := fun (P Q : e -> prop) (x : e) => (P x) and (Q x).
        Infix "that"        := s_that (at level 80) : sem_scope.
        Definition pex      : (e -> prop) -> prop   := p_exists ent.
        Definition pfa      : (e -> prop) -> prop   := p_forall ent.
        Definition some     : (e -> prop) -> (e -> prop) -> prop := fun P Q : e -> prop => pex (P that Q).
        Definition every    : (e -> prop) -> (e -> prop) -> prop := fun P Q : e -> prop => pfa (fun x : e => (P x) implies (Q x)).

    (* preorder stuff *)
        Definition p_entails : prop -> prop -> Prop := fun p q : prop => forall w : world, p@w = true -> q@w = true.
        Infix "entails" := p_entails (at level 80) : sem_scope.
        Definition p_equiv : prop -> prop -> Prop := fun p q : prop => (p entails q) /\ (q entails p).
        Infix "≡" := p_equiv (at level 80) : sem_scope.

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
        :=  fun (A : Type) (n : nat) (v : Vect A (S n)) => match v in (Vect _ m) return (if m then unit else A) with [] => tt | x :: _ => x end.

    Definition tail : forall {A : Type} {n : nat}, Vect A (S n) -> Vect A n
        :=  fun (A : Type) (n : nat) (v : Vect A (S n)) => match v in (Vect _ m) return (match m with 0 => unit | S k => Vect A k end) with [] => tt | _ :: xs => xs end.

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

(* meta-proofs over equality *)
    Definition refl_l_id_trans : forall {A : Type} {x y : A} (e : x = y), e = (eq_trans eq_refl e)
        := fun (A : Type) (x : A) => eq_ind_dep x (fun (z : A) (d : x = z) => d = eq_trans eq_refl d) eq_refl.
    Definition refl_r_id_trans': forall {A : Type} {x y : A} (e : x = y), (eq_sym e) = (eq_trans' e eq_refl)
        := fun (A : Type) (x : A) => eq_ind_dep x (fun (z : A) (d : x = z) => (eq_sym d) = (eq_trans' d eq_refl)) eq_refl.
    Definition feq_comp : forall {A B C : Type} (f : B -> C) (g : A -> B) {x y : A} (e : x = y), (feq f (feq g e)) = (feq (f∘g) e)
        := fun (A B C : Type) (f : B -> C) (g : A -> B) (x : A) => eq_ind_dep x (fun (z : A) (d : x = z) => (feq f (feq g d)) = (feq (f∘g) d)) eq_refl.
    Definition feqovertrans : forall {A B : Type} (f : A -> B) {x y z : A} (p : x = y) (q : y = z), (eq_trans (feq f p) (feq f q)) = (feq f (eq_trans p q))
        := fun (A B : Type) (f : A -> B) (x y z : A) (p : x = y) => eq_ind_dep y (fun (k : A) (q : y = k) => (eq_trans (feq f p) (feq f q)) = (feq f (eq_trans p q))) eq_refl z.
    Definition eq_rect_f1   : forall {A B : Type} (P : A -> Type) {x : A} (f : P x -> B) {y : A} (e : x = y) (p : P y), (eq_rect x (fun z : A => P z -> B) f y e p) = (f (eq_rect y P p x (eq_sym e)))
        :=  fun (A B : Type) (P : A -> Type) (x : A) (f : P x -> B) =>
            eq_ind_dep x (fun (y : A) (d : x = y) => forall p : P y, (eq_rect x (fun z : A => P z -> B) f y d p) = (f (eq_rect y P p x (eq_sym d)))) (fun p : P x => eq_refl).
    Definition eq_rect_f2   : forall {A B : Type} (P : A -> Type) {x : A} (f : B -> P x) (b : B) {y : A} (e : x = y), (eq_rect x (fun z : A => B -> P z) f y e b) = (eq_rect x P (f b) y e)
        := fun (A B : Type) (P : A -> Type) (x : A) (f : B -> P x) (b : B) => eq_ind_dep  x (fun (y : A) (d : x = y) => (eq_rect x (fun z : A => B -> P z) f y d b) = (eq_rect x P (f b) y d)) eq_refl.
    Definition eq_rect_f3   : forall {A : Type} (P Q : A -> Type) {x : A} (f : P x -> Q x) {y : A} (e : x = y) (p : P y), (eq_rect x (fun z : A => P z -> Q z) f y e p) = (eq_rect x Q (f (eq_rect y P p x (eq_sym e))) y e)
        :=  fun (A : Type) (P Q : A -> Type) (x : A) (f : P x -> Q x) =>
            eq_ind_dep x (fun (y : A) (d : x = y) => forall p : P y, (eq_rect x (fun z : A => P z -> Q z) f y d p) = (eq_rect x Q (f (eq_rect y P p x (eq_sym d))) y d)) (fun p : P x => eq_refl).
    Definition eq_rect_feq  : forall {A B : Type} (P : B -> Type) (f : A -> B) {x : A} (p : P (f x)) {y : A} (d : x = y), (eq_rect (f x) P p (f y) (feq f d)) = (eq_rect x (P∘f) p y d)
        :=  fun (A B : Type) (P : B -> Type) (f : A -> B) (x : A) (p : P (f x)) => eq_ind_dep x (fun (y : A) (d : x = y) => (eq_rect (f x) P p (f y) (feq f d)) = (eq_rect x (P∘f) p y d)) eq_refl.
    Definition trans_inv1   : forall {A : Type} {x y : A} (p : x = y), (eq_trans (eq_sym p) p) = eq_refl
        := fun (A : Type) (x : A) => eq_ind_dep x (fun (y : A) (p : x = y) => (eq_trans (eq_sym p) p) = eq_refl) eq_refl.
    Definition trans_inv2   : forall {A : Type} {x y : A} (p : x = y), (eq_trans p (eq_sym p)) = eq_refl
        := fun (A : Type) (x : A) => eq_ind_dep x (fun (y : A) (p : x = y) => (eq_trans p (eq_sym p)) = eq_refl) eq_refl.
    Definition trans'_inv   : forall {A : Type} {x y : A} (p : x = y), (eq_trans' p p) = eq_refl
        := fun (A : Type) (x : A) => eq_ind_dep x (fun (y : A) (p : x = y) => (eq_trans' p p) = eq_refl) eq_refl.
    Definition feqoversym   : forall {A B : Type} (f : A -> B) {x y : A} (d : x = y), (feq f (eq_sym d)) = (eq_sym (feq f d))
        := fun (A B : Type) (f : A -> B) (x : A) => eq_ind_dep x (fun (y : A) (d : x = y) => (feq f (eq_sym d)) = (eq_sym (feq f d))) eq_refl.

(* Basic nat/addition proofs *)
    Definition Zria         : forall n : nat, (n+0) = n
        := nat_ind (fun n : nat => (n+0) = n) eq_refl (fun i : nat => feq S).
    Definition Sdistr       : forall m j : nat, (S (m+j)) = (m+(S j))
        := fun m j : nat => nat_ind (fun i : nat => (S (i+j)) = (i+(S j))) eq_refl (fun i : nat => feq S) m.
    Definition add_comm     : forall m n : nat, (m+n) = (n+m)
        :=  fun m : nat => nat_ind (fun n : nat => (m+n) = (n+m)) (Zria m) (fun (j : nat) (e : (m+j) = (j+m)) => eq_trans' (Sdistr m j) (feq S e)).
    Definition add_assoc    : forall m n k : nat, (m+(n+k)) = ((m+n)+k)
        := fun m n k : nat => nat_ind (fun i : nat => (i+(n+k)) = ((i+n)+k)) eq_refl (fun i : nat => feq S) m.
    Definition assoc_flip   : forall m n k : nat, ((m+n)+k) = ((m+k)+n)
        := fun m n k : nat => nat_ind (fun i : nat => ((i+n)+k) = ((i+k)+n)) (add_comm n k) (fun i : nat => feq S) m.

(* Vect proofs *)
    Definition Vect_form : forall {A : Type} {n : nat} (v : Vect A n), (match n as m return (Vect A m -> Prop) with 0 => eq [] | S i => fun u : Vect A (S i) => ((head u)::(tail u)) = u end) v
        :=  fun (A : Type) (n : nat) (v : Vect A n) =>
            match v as u in (Vect _ k) return ((match k as m return (Vect A m -> Prop) with 0 => eq [] | S i => fun l : Vect A (S i) => ((head l)::(tail l)) = l end) u)
            with [] => eq_refl | x::xs => eq_refl end.

    (* "vcast narrowing" *)
    Definition vcstnrw      : forall {A : Type} {m : nat} (v : Vect A (S m)) {n : nat} (e : m = n), (vcast v (feq S e)) = ((head v)::(vcast (tail v) e))
        := fun (A : Type) (m : nat) (v : Vect A (S m)) => eq_ind_dep m (fun (n : nat) (d : m = n) => (vcast v (feq S d)) = ((head v)::(vcast (tail v) d))) (eq_sym (Vect_form v)).
    Definition vcsttrans    : forall {A : Type} {m : nat} (v : Vect A m) {n k : nat} (p : m = n) (q : n = k), (vcast (vcast v p) q) = (vcast v (eq_trans p q))
        := fun (A : Type) (m : nat) (v : Vect A m) (n k : nat) (p : m = n) => eq_ind_dep n (fun (z : nat) (q : n = z) => (vcast (vcast v p) q) = (vcast v (eq_trans p q))) eq_refl k.
    Definition vcstinj      : forall {A : Type} {m : nat} (u v : Vect A m) {n : nat} (e : m = n), (vcast u e) = (vcast v e) -> u = v
        := fun (A : Type) (m : nat) (u v : Vect A m) => eq_ind_dep m (fun (n : nat) (d : m = n) => (vcast u d) = (vcast v d) -> u = v) id.

    Definition take_assoc   : forall {A : Type} (m n k : nat) (v : Vect A (m+(n+k))), (take m v) = (take m (take (m+n) (vcast v (add_assoc m n k))))
        :=  fun (A : Type) (m n k : nat) =>
            nat_ind (fun i : nat => forall v : Vect A (i+(n+k)), (take i v) = (take i (take (i+n) (vcast v (add_assoc i n k)))))
                    (fun _ : Vect A (n+k) => eq_refl)
                    (fun (i : nat) (f : forall r : Vect A (i+(n+k)), (take i r) = (take i (take (i+n) (vcast r (add_assoc i n k))))) (v : Vect A (S (i+(n+k)))) =>
                        eq_trans (feq (vcons (head v)) (f (tail v))) (eq_sym (feq (fun u : Vect A (S ((i+n)+k)) => (head u)::(take i (take (i+n) (tail u)))) (vcstnrw v (add_assoc i n k)))))
                    m.
    Definition drop_assoc   : forall {A : Type} (m n k : nat) (v : Vect A ((m+n)+k)), (drop (m+n) v) = (drop n (drop m (vcast v (eq_sym (add_assoc m n k)))))
        :=  fun (A : Type) (m n k : nat) =>
            nat_ind (fun i : nat => forall v : Vect A ((i+n)+k), (drop (i+n) v) = (drop n (drop i (vcast v (eq_sym (add_assoc i n k))))))
                    (fun v : Vect A (n+k) => eq_refl)
                    (fun (i : nat) (f : forall r : Vect A ((i+n)+k), (drop (i+n) r) = (drop n (drop i (vcast r (eq_sym (add_assoc i n k)))))) (v : Vect A (S ((i+n)+k))) =>
                        eq_trans    (f (tail v))
                                    (eq_trans'  (feq (fun u : Vect A (S (i+(n+k))) => drop n (drop i (tail u))) (vcstnrw v (eq_sym (add_assoc i n k))))
                                                (feq (fun d : (S ((i+n)+k)) = (S (i+(n+k))) => drop n (drop i (tail (vcast v d)))) (feqoversym S (add_assoc i n k)))))
                    m.
    Definition take_assoc2  : forall {A : Type} (m n k : nat) (v : Vect A (m+(n+k))), ((take m v) ++ (take n (drop m v))) = (take (m+n) (vcast v (add_assoc m n k)))
        :=  fun (A : Type) (m n k : nat) =>
            nat_ind (fun i : nat => forall v : Vect A (i+(n+k)), ((take i v) ++ (take n (drop i v))) = (take (i+n) (vcast v (add_assoc i n k))))
                    (fun v : Vect A (n+k) => eq_refl)
                    (fun (i : nat) (f : forall r : Vect A (i+(n+k)), ((take i r) ++ (take n (drop i r))) = (take (i+n) (vcast r (add_assoc i n k)))) (v : Vect A (S (i+(n+k)))) =>
                        eq_trans (feq (vcons (head v)) (f (tail v))) (eq_sym (feq (fun u : Vect A (S ((i+n)+k)) => (head u)::(take (i+n) (tail u))) (vcstnrw v (add_assoc i n k)))))
                    m.

    Definition Nriap        : forall {A : Type} {n : nat} (v : Vect A n), v = (vcast (v ++ []) (Zria n))
        :=  fun A : Type =>
            Vect_ind A  (fun (n : nat) (v : Vect A n) => v = (vcast (v ++ []) (Zria n))) eq_refl
                        (fun (i : nat) (x : A) (r : Vect A i) (e : r = (vcast (r ++ []) (Zria i))) =>
                            eq_trans (feq (vcons x) e) (eq_ind_dep (i+0) (fun (z : nat) (d : (i+0) = z) => (x::(vcast (r ++ []) d)) = (vcast (x::(r ++ [])) (feq S d))) eq_refl i (Zria i))).
    Definition Nriap2       : forall {A : Type} {n : nat} (v : Vect A (n+0)), ((vcast v (Zria n)) ++ []) = v
        :=  fun A : Type =>
            nat_ind (fun n : nat => forall v : Vect A (n+0), ((vcast v (Zria n)) ++ []) = v)
                    (fun v : Vect A 0 => eq_ind [] (fun u : Vect A 0 => (u ++ []) = u) eq_refl v (Vect_form v))
                    (fun (j : nat) (f : forall r : Vect A (j+0), ((vcast r (Zria j)) ++ []) = r) (v : Vect A (S (j+0))) =>
                        eq_trans (feq (flip append []) (vcstnrw v (Zria j))) (eq_trans (feq (vcons (head v)) (f (tail v))) (Vect_form v))).

    Definition tkdr_app_inv : forall {A : Type} (m : nat) {n : nat} (v : Vect A (m+n)), v = ((take m v) ++ (drop m v))
        :=  fun (A : Type) (m n : nat) =>
            nat_ind (fun i : nat => forall v : Vect A (i+n), v = ((take i v) ++ (drop i v)))
                    (@eq_refl (Vect A n))
                    (fun (i : nat) (f : forall r : Vect A (i+n), r = ((take i r) ++ (drop i r))) (v : Vect A (S (i+n))) => eq_trans' (Vect_form v) (feq (vcons (head v)) (f (tail v)))) m.

    (* take/drop of a vector (l++r) is equal to l/r, respectively *)
    Definition tkdr_app_inv2a : forall {A : Type} (m : nat) {n : nat} (u : Vect A m) (v : Vect A n), u = (take m (u ++ v))
        := fun (A : Type) (m n : nat) (u : Vect A m) (v : Vect A n) => Vect_ind A (fun (i : nat) (l : Vect A i) => l = (take i (l ++ v))) eq_refl (fun (i : nat) (x : A) (l : Vect A i) => feq (vcons x)) m u.
    Definition tkdr_app_inv2b : forall {A : Type} (m : nat) {n : nat} (u : Vect A m) (v : Vect A n), v = (drop m (u ++ v))
        := fun (A : Type) (m n : nat) (u : Vect A m) (v : Vect A n) => Vect_ind A (fun (i : nat) (l : Vect A i) => v = (drop i (l ++ v))) eq_refl (fun (i : nat) (_ : A) (l : Vect A i) => id) m u.

    (* functional versions! *)
    Definition tkdr_app_inv3a : forall {A : Type} {n m : nat} (v : Vect A m), (fun u : Vect A n => take m (v ++ u)) = (fun _ : Vect A n => v)
        :=  fun (A : Type) (n : nat) =>
            Vect_ind A (fun (m : nat) (v : Vect A m) => (fun u : Vect A n => take m (v ++ u)) = (fun _ : Vect A n => v)) eq_refl (fun (i : nat) (x : A) (l : Vect A i) => feq (comp (vcons x))).
    Definition tkdr_app_inv3b : forall {A : Type} {n m : nat} (v : Vect A m), (fun u : Vect A n => drop m (v ++ u)) = id
        := fun (A : Type) (n : nat) => Vect_ind A (fun (m : nat) (v : Vect A m) => (fun u : Vect A n => drop m (v ++ u)) = id) eq_refl (fun (i : nat) (x : A) (l : Vect A i) => id).

    Definition vapp0        : forall {A : Type} {m : nat} (v : Vect A (m+0)), ((take m v) ++ []) = v
        :=  fun A : Type =>
            nat_ind (fun m : nat => forall v : Vect A (m+0), ((take m v) ++ []) = v) Vect_form
                    (fun (i : nat) (f : forall r : Vect A (i+0), ((take i r) ++ []) = r) (v : Vect A (S (i+0))) => eq_trans (feq (vcons (head v)) (f (tail v))) (Vect_form v)).

    Definition vcsttke      : forall {A : Type} {m n : nat} (v : Vect A (m+n)) {k : nat} (d : m = k), (vcast (take m v) d) = (take k (vcast v (feq (flip plus n) d)))
        := fun (A : Type) (m n : nat) (v : Vect A (m+n)) => eq_ind_dep  m (fun (k : nat) (d : m = k) => (vcast (take m v) d) = (take k (vcast v (feq (flip plus n) d)))) eq_refl.

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
                        match n as j,p as k return ((max (max (S i) j) k) = (max (S i) (max j k))) with S j,S k => feq S (f j k) | _,_ => eq_refl end).
    Definition max_comm : forall m n : nat, (max m n) = (max n m)
        :=  nat_ind (fun m : nat => forall n : nat, (max m n) = (max n m)) (fun n : nat => eq_sym (Zrix n))
                    (fun (i : nat) (f : forall j : nat, (max i j) = (max j i)) (n : nat) => match n as j return ((max (S i) j) = (max j (S i))) with 0 => eq_refl | S j => feq S (f j) end).

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
        :=  fun m n k : nat => eq_trans (feq2 max (add_comm m k) (add_comm n k)) (eq_trans (max_add m n k) (add_comm k (max m n))).

    Definition max_succ     : forall m : nat, (max m (S m)) = (S m)
        := nat_ind (fun m : nat => (max m (S m)) = (S m)) eq_refl (fun i : nat => feq S).

(* Other (meta-)proofs *)
    Definition feqSZria     : forall (m n : nat) (p : m = n), (feq (flip plus 0) (feq S p)) = (feq S (feq (flip plus 0) p))
        := fun (m n : nat) (p : m = n) => eq_trans (feq_comp (flip plus 0) S p) (eq_sym (feq_comp S (flip plus 0) p)).
    Definition dist0isidem  : forall m : nat, (max_dist 0 0 m) = (max_idem m)
        := nat_ind (fun m : nat => (max_dist 0 0 m) = (max_idem m)) eq_refl (fun i : nat => feq (feq S)).
    Definition Zrvsadas00   : forall m : nat, (Zria (m+0)) = (eq_sym (add_assoc m 0 0))
        :=  nat_ind (fun m : nat => (Zria (m+0)) = (eq_sym (add_assoc m 0 0))) eq_refl
                    (fun (i : nat) (d : (Zria (i+0)) = (eq_sym (add_assoc i 0 0))) => eq_trans (feq (feq S) d) (feqoversym S (add_assoc i 0 0))).

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
                        (fun i : nat => feq (fun s : {x : nat | (max i i) = (i+x)} => let (x,p) := s in exist (fun y : nat => (S (max i i)) = (S (i+y))) x (feq S p))).

(* DyCG Types *)
    Notation "'e^' n" := (Vect e n) (at level 0) : vect_scope.
    Definition con : nat -> Set := fun n : nat => e^n -> prop.

    Definition xon : nat -> nat -> Set := fun m i : nat => con m -> con (m+i).
    Definition kon : nat -> nat -> Set := fun m i : nat => forall n : nat, xon (m+n) i.

    Fixpoint p_i (n : nat) {struct n} : Set := match n with 0 => prop | S i => e -> p_i i end.

    Definition udy' : (nat -> nat) -> nat -> nat -> Set
        := fun (f : nat -> nat) (n i : nat) => forall u : Vect nat n, xon (f (vmax u)) i.
    Definition udy  : nat -> nat -> nat -> Set := udy'∘max.

    Fixpoint dy' (f : nat -> nat) (n i : nat) {struct n} : Set
        :=  match n with
                | 0     => xon (f 0) i
                | S j   => forall m : nat, dy' (f∘(max (S m))) j i
            end.
    Definition dy : nat -> nat -> nat -> Set := dy'∘max.

(* Casts & exts *)
    Definition ccast : forall {m : nat}, con m -> forall {n : nat}, m = n -> con n
        := fun m : nat => eq_rec m con.
        (* := fun (m : nat) (c : con m) (n : nat) (d : m = n) (v : e^n) => c (vcast v (eq_sym d)). *)
    Definition xcast : forall {m i : nat}, xon m i -> forall {n : nat}, m = n -> xon n i
        := fun m i : nat => eq_rec m (flip xon i).
        (* :=  fun (m i : nat) (k : xon m i) (n : nat) (d : m = n) (c : con n) (v : e^(n+i)) =>
            k (ccast c (eq_sym d)) (vcast v (eq_sym (feq (flip plus i) d))). *)
    Definition kcast : forall {m i : nat}, kon m i -> forall {n : nat}, m = n -> kon n i
        := fun m i : nat => eq_rec m (flip kon i).
        (* :=  fun (m i : nat) (k : kon m i) (n : nat) (d : m = n) (c : con n) (v : e^(n+i)) =>
            k (ccast c (eq_sym d)) (vcast v (eq_sym (feq (flip plus i) d))). *)

    Definition cext : forall i : nat, kon 0 i := fun (i n : nat) (c : con n) (v : e^(n+i)) => c (take n v).
    Notation "c ⁺" := (cext 1 _ c) (at level 0) : dyn_scope.
    Open Scope dyn_scope.
    Definition kext : forall {m i : nat}, xon m i -> kon m i
        :=  fun (m i : nat) (k : xon m i) (n : nat) (c : con (m+n)) (v : e^((m+n)+i)) =>
            (* v ≈ ((l ++ u) ++ r) *)
            let l := (take m (take (m+n) v)) in
            let u := (drop m (take (m+n) v)) in
            let r := (drop (m+n) v) in
            k (fun t : e^m => c (t ++ u)) (l ++ r).

    Definition dy1ext : forall {m i : nat}, dy m 1 i -> forall n : nat, dy (max m n) 1 i
        :=  fun (m i : nat) (D : dy m 1 i) (n j : nat) => let (y,q) := (k_frnt n (max m (S j))) in xcast (kext (D j) y) (eq_trans' q (eq_trans' (max_assoc n m (S j)) (feq (flip max (S j)) (max_comm n m)))).

(* cc & d_AND *)
    Definition cc : forall {m i : nat}, xon m i -> xon m i
        := fun (m i : nat) (k : xon m i) (c : con m) (v : e^(m+i)) => (c (take m v)) and (k c v).

    Definition d_AND : forall {m i j : nat}, xon m i -> xon (m+i) j -> xon m (i+j)
        :=  fun (m i j : nat) (h : xon m i) (k : xon (m+i) j) (c : con m) (v : e^(m+(i+j))) =>
            let u := (vcast v (add_assoc m i j)) in (h c (take (m+i) u)) and (k (cc h c) u).
    Infix "AND" := d_AND (at level 20) : dyn_scope.

(* dynamicizers *)
    Fixpoint udyn (k : nat) {struct k} : p_i k -> udy 0 k 0
        :=  match k as m return (p_i m -> udy 0 m 0) with
                | 0     =>  fun (p : prop) (_ : Vect nat 0) (_ : con 0) (_ : e^0) => p
                | S i   =>  fun (P : e -> p_i i) (u : Vect nat (S i)) (c : con (vmax u)) (v : e^((vmax u)+0)) =>
                            let (x,p) := (h_frnt (S (head u)) (vmax (tail u))) in
                            let (y,q) := (k_frnt (S (head u)) (vmax (tail u))) in
                            kext    (udyn i (P (nth (head u) (vcast v (eq_trans (Zria (vmax u)) p)))) (tail u))
                                    y (ccast c q) (vcast v (feq (flip plus 0) q))
            end.

    Fixpoint udytody (f : nat -> nat) (k i : nat) {struct k} : udy' f k i -> dy' f k i
        :=  match k as j return (udy' f j i -> dy' f j i) with
                | 0     =>  fun g : Vect nat 0 -> xon (f 0) i => g []
                | S j   =>  fun (g : forall u : Vect nat (S j), xon (f (vmax u)) i) (m : nat) =>
                            udytody (f∘(max (S m))) j i (fun r : Vect nat j => g (m::r))
            end.

    Definition dyn  : forall k : nat, p_i k -> dy  0 k 0 := fun (k : nat) (P : p_i k) => udytody id k 0 (udyn k P).

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
                            (fun (k n : nat) (r : Vect nat k) (g : forall (h : nat -> nat) (E : udy' h k i), (dytoudy h k i (udytody h k i E) r) = (E r))
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


(* up_AND' : forall (p : nat -> nat) (x y z : nat) (q : nat -> nat -> nat -> nat), udy' p x y -> udy' (q x y) x z -> udy' p x (y+z)
f : nat -> nat
k,i,j,n : nat
g : nat -> nat -> nat -> nat
D : udy' f (S k) i
E : udy' (g (S k) i) (S k) j
r : Vect nat k
============================
xon (f (max (S n) (vmax r))) (i+j)


(up_AND' (f∘(max (S n))) k i j (fun x y : nat => (g (S x) y)∘(max (S n))) (fun t : Vect nat k => D (n::t)) (fun t : Vect nat k => E (n::t)) r) : xon (f (max (S n) (vmax r))) (i+j) *)


(* A version of the generalized predicate conjunction that works! Unfortunately, won't be able to coerce the types into regular dy form *)

Definition p_AND' : forall (k i j : nat) (f : nat -> nat), dy' f k i -> dy' ((flip plus i)∘f) k j -> dy' f k (i+j)
    :=  fun k i j : nat =>  nat_rec (fun z : nat => forall f : nat -> nat, dy' f z i -> dy' ((flip plus i)∘f) z j -> dy' f z (i+j))
                                    (fun f : nat -> nat => @d_AND (f 0) i j)
                                    (fun (z : nat) (IH : forall g : nat -> nat, dy' g z i -> dy' ((flip plus i)∘g) z j -> dy' g z (i+j)) (f : nat -> nat)
                                         (D : dy' f (S z) i) (E : dy' ((flip plus i)∘f) (S z) j) (n : nat) => IH (f∘(max (S n))) (D n) (E n))
                                    k.

(* Other Definitions needed for donkey sentence *)
    Fixpoint vexists {n : nat} : con n -> prop
        :=  match n as k return (con k -> prop) with
                | 0     =>  fun c : con 0 => c []
                | S i   =>  fun c : con (S i) => pex (fun x : e => vexists (fun v : e^i => c (x::v)))
            end.

    Definition NOT : forall {m i : nat}, xon m i -> xon m 0
        :=  fun (m i : nat) (k : xon m i) (c : con m) (v : e^(m+0)) =>
            not (vexists (fun u : e^i => k c ((take m v) ++ u))).

    Definition d_OR : forall {m i j : nat}, xon m i -> xon m j -> xon m 0
        := fun (m i j : nat) (h : xon m i) (k : xon m j) => NOT ((NOT h) AND (NOT (kext k 0))).
    Infix "OR" := d_OR (at level 0) : dyn_scope.

    Definition d_IMPLIES : forall {m i j : nat}, xon m i -> xon (m+i) j -> xon m 0
        := fun (m i j : nat) (h : xon m i) (k : xon (m+i) j) => (NOT h) OR (h AND k).
    Infix "IMPLIES" := d_IMPLIES (at level 20) : dyn_scope.

(* Dynamic Quantifiers *)
    Definition EXISTS : forall {m i : nat}, dy m 1 i -> xon m (S i)
        :=  fun (m i : nat) (D : dy m 1 i) (c : con m) (v : e^(m+(S i))) => xcast (D m) (eq_trans (feq (max m) (add_comm 1 m)) (max_plus m 1)) c⁺ (vcast v (add_assoc m 1 i)).
    Definition FORALL : forall {m i : nat}, dy m 1 i -> xon m 0
        := fun (m i : nat) (D : dy m 1 i) => NOT (EXISTS (fun j : nat => NOT (D j))).

    Definition dTHAT : forall {m i j : nat}, dy m 1 i -> dy' ((flip plus i)∘(max m)) 1 j -> dy m 1 (i+j)
        := fun m i j : nat => p_AND' 1 i j (max m).
        (* :=  fun (m i j : nat) (D : dy m 1 i) (E : dy (m+i) 1 j) (n : nat) => (D n) AND (kcast (E (n+i)) (max_k_plus m (S n) i)). *) (* old, bad definition *)
    Infix "THAT" := dTHAT (at level 20) : dyn_scope.

    Definition SOME  : forall {m i j : nat}, dy m 1 i -> dy' ((flip plus i)∘(max m)) 1 j -> xon m (S (i+j))
        := fun (m i j : nat) (D : dy m 1 i) (E : dy' ((flip plus i)∘(max m)) 1 j) => EXISTS (D THAT E).

    Definition EVERY : forall {m i j : nat}, dy m 1 i -> dy' ((flip plus i)∘(max m)) 1 j -> xon m 0
        :=  fun (m i j : nat) (D : dy m 1 i) (E : dy' ((flip plus i)∘(max m)) 1 j) => FORALL (fun n : nat => (D n) IMPLIES (E n)).

    Definition IT       : forall (n : nat) {m i : nat}, dy m 1 i -> xon (max m (S n)) i
        := fun (n m i : nat) (D : dy m 1 i) => D n.

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



Definition the_donkey_sentence : xon 0 0
    :=  EVERY   (FARMER THAT (fun m : nat => SOME (dy1ext DONKEY (S (m+0))) (fun n : nat => xcast (OWN (m+0) n) (feq S (eq_sym (Zria (max (m+0) n)))))))
                (fun m : nat => xcast (IT (S m) (BEAT m)) (feq S (eq_trans (max_succ m) (eq_trans (feq S (eq_sym (Zria m))) (Sdistr m 0))))).


(* Eval compute in (the_donkey_sentence OutBlue []).
    = not p_exists ent (fun x : e => not (not ((not (not p_exists ent (fun x0 : e => farmer x and (donkey x0 and own x x0)))) and (not p_exists ent (fun x0 : e => (farmer x and (donkey x0 and own x x0)) and beat x x0)))))
    : prop
    = not (pex (fun x : e => not (not ((not (not (pex (fun y : e => (farmer x) and ((donkey y) and (own x y)))))) and (not (pex (fun y : e => ((farmer x) and ((donkey y) and (own x y))) and (beat x y))))))))
    ≡ not (pex (fun x : e => (pex (fun y : e => (farmer x) and ((donkey y) and (own x y)))) and (not (pex (fun y : e => ((farmer x) and ((donkey y) and (own x y))) and (beat x y))))))
    ≡ pfa (fun x : e => (pex (fun y : e => (farmer x) and ((donkey y) and (own x y)))) implies (pex (fun y : e => ((farmer x) and ((donkey y) and (own x y))) and (beat x y))))

Hurray! This works!!! *)

(* same as above, but with all of the implicit arguments given explicitly (except the proofs used in the castings) *)
Definition the_donkey_sentence_args_exp : xon 0 0
    :=  @EVERY 0 1 0
            (@dTHAT 0 0 1 FARMER
                (fun m : nat => @SOME (S (m+0)) 0 0 (@dy1ext 0 0 DONKEY (S (m+0))) (fun n : nat => @xcast (S (max (m+0) n)) 0 (OWN (m+0) n) (S ((max (m+0) n)+0)) (eq_sym (feq S (Zria (max (m+0) n)))))))
            (fun m : nat => @xcast (S (max m (S m))) 0 (@IT (S m) (S m) 0 (BEAT m)) (S (m+1)) (feq S (eq_trans (max_succ m) (eq_trans (eq_sym (feq S (Zria m))) (Sdistr m 0))))).


(* notes from doing QP1 draft 1 *)
    (* provable, but haven't done so officially. Besides, what I have to do to the second conjunct to get it to work is a bit ridiculous. I'll add that such a theorem exists as a footnote *)
    (* kextAND : ∀m,n,i,j:nat.∀h:xon m i.∀k:xon (m+i) j.∀c:con (m+n).∀w^m,x^n,y^i,z^j.[(kext_[m,i+j] (h AND_[m,i,j] k) n c (((w,x),(y,z)))) = ((kext_[m,i] h n) AND_[m+n,i,j] (λd:con ((m+n)+i).λr^m,s^n,t^i,u^j.kext_[m+i,j] k n (λa^m,b^i,t^n.d ((a,t),b)) (((r,t),s),u)) c ((w,x),(y,z)))] *)
    (* version of SOME as (SOME D E) ≈ ((EXISTS D) AND (E m)) *)
    (* SOME : forall m i j : nat, dy m 1 i -> dy (S (m+i)) 1 j -> xon m (S (i+j)) *)
    (* SOME := λm,i,j:nat.λD:dy m 1 i.λE:dy (S (m+i)) 1 j.(EXISTS_[m,i] D) AND_[m,S i,j] (xcast_[S (max (m+i) m),j] (E m) (m+(S i)) (eq_trans (feq S (eq_trans (max_comm (m+i) m) (max_plus m i))) (Sdistr m i))) *)

