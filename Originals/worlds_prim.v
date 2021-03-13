(* worlds_prim *)

Load CDS_primitives.
Open Scope sem_scope.

Axiom world : Set. (* again, to allow the use of w as a (meta-)variable over this type *)
Axiom tv    : prop -> world -> bool.
Axiom w₀    : world.

Definition p_entails (p q : prop) : Prop := forall w : world, ((tv p w) = true) -> ((tv q w) = true).
Infix "entails" := p_entails (at level 50) : sem_scope.
Definition p_equiv (p q : prop) : Prop := (p entails q) /\ (q entails p).
Infix "≡" := p_equiv (at level 40) : sem_scope.
Definition facts : world -> prop -> bool := fun (w : world) (p : prop) => tv p w.

Open Scope bool_scope.
Infix    "→"    := implb    (at level 50) : bool_scope.
Notation "¬ x"  := (negb x) (at level 50) : bool_scope.

(* Move into CDS_primitives? *)
Definition pset : Set := prop -> bool.
Section Ultra.
    Variable s : pset.

    Definition uc  : Prop := forall p q : prop, ((s p) = true) -> (p entails q) -> ((s q) = true).
    Definition ac  : Prop := forall p q : prop, ((s p) = true) -> ((s q) = true) -> ((s (p and q)) = true).
    Definition sai : Prop := forall p   : prop, ((s p) = true) \/ ((s (not p)) = true).
    Definition cst : Prop := (s falsity) = false.
    Definition ultrafilter : Prop := uc /\ ac /\ sai /\ cst.
End Ultra.

(* Axiomatizing the prop connectives *)
Section prop_axioms.
    Variables (R : prop -> prop) (p q : prop) (w : world).

    Axiom p_and_ax      : (tv (p  and    q) w) = ((tv p w) && (tv q w)).
    Axiom p_or_ax       : (tv (p   or    q) w) = ((tv p w) || (tv q w)).
    Axiom p_implies_ax  : (tv (p implies q) w) = ((tv p w) →  (tv q w)).
    Axiom truth_ax      : (tv truth w) = true.
    Axiom falsity_ax    : (tv falsity w) = false.
    Axiom p_not_ax      : (tv (not p) w) = (¬ (tv p w)).
    Axiom p_iff_ax      : (tv (p iff q) w) = ((tv (p implies q) w) && (tv (q implies p) w)).
    Axiom p_equals_ax   : ((tv (p equals q) w) = true) <-> (p = q). (* do we need the only-if part? *)
    Axiom p_exists_ax   : ((tv (p_exists R) w) = true) <-> (exists p : prop, (tv (R p) w) = true).
    Axiom p_forall_ax   : ((tv (p_forall R) w) = true) <-> (forall p : prop, (tv (R p) w) = true).

    Axiom fact_inj : forall w v : world, (facts w) = (facts v) -> w = v.
    Axiom all_ultras_worlds : forall s : pset, (ultrafilter s) -> exists w : world, s = (facts w).
        (*  question: "exists w : world, s = (facts w)" or {w : world | s = (facts w)}?
            Aka, to we want to be able to access this world for reasons other than theorem proving or not? *)
    (* won't concern ourselves with this for now *)
    (* Axiom stone_rep : ~(p entails q) -> exists w : world, (tv p w) = true /\ (tv q w) = false. *)
End prop_axioms.

Section Bool_theorems.
    Variable s t : bool.

    (* my first definition with implicit arguments *)
    Definition eq_trans' : forall {A : Type} {x y z : A}, x = y -> x = z -> y = z :=
        fun (A : Type) (x y z : A) (u : x = y) => eq_trans (eq_sym u).

    Definition bande1 : (s && t) = true -> s = true := bool_ind (fun b : bool => (b && t) = true -> b = true)
        (fun _ : t = true => eq_refl) (fun e : false = true => e) s.
        (* (fun _ : (true∧t) = true => eq_refl) (fun e : (false∧t) = true => e) s. *)
        (* (fun _ : t = true => eq_refl) id s *)

    Definition bande2 : (s && t) = true -> t = true
        := bool_ind (fun b : bool => (b && t) = true -> t = true) (fun e : t = true => e)
            (fun c : false = true => bool_ind (fun d : bool => d = true) eq_refl c t) s.
        (* := bool_ind (fun b : bool => (b && t) = true -> t = true) (fun e : (true && t) = true => e)
            (fun c : (false && t) = true => bool_ind (fun d : bool => d = true) eq_refl c t) s. *)
        (* fun c : (false∧t) = true => eq_ind false (fun d : bool => if d then (t = true) else True) I true c *)
        (* fun c : false = true => eq_ind false (fun d : bool => if d then (t = true) else True) I true c *)

    Definition bandi (u : s = true) (v : t = true) : (s && t) = true := f_equal2 andb u v.
        (* eq_ind_r (x := true) (fun b : bool => (b∧t)=true) v u *)

    (* Written like this since Coq was rejecting its own proofs- why implicits annoy me! *)
    Definition bore : (s || t) = true -> (s = true) \/ (t = true)
        := bool_ind (fun b : bool => (b || t) = true -> b = true \/ t = true) (or_introl (B := _)) (or_intror (B := _)) s.
        (* := bool_ind (fun b : bool => (b || t) = true -> b = true \/ t = true)
            (fun _ : (true || t) = true => or_introl eq_refl) (or_intror (B := _)) s. *)
        (* if s as b return ((b∨t) = true -> b = true \/ t = true) then (or_introl (B := _)) else (or_intror (B := _)) *)

    Definition boreind (u : bool) (e : (s || t) = true) (f : s = true -> u = true) (g : t = true -> u = true) : u = true
        := or_ind f g (bore e).

    Definition bori1    : s = true -> (s || t) = true := f_equal (fun b : bool => b || t) (y := true).
        (* eq_ind_r (x := true) (fun b : bool => (b∨t) = true) eq_refl (y := s) *)

    Definition bori2    : t = true -> (s || t) = true := fun e : t = true => bool_ind (fun b : bool => (b || t) = true) eq_refl e s.

    Definition false_not_true : false <> true := eq_ind false (fun e : bool => if e then False else True) I true.

    Definition boolcantbeboth : s = false -> s <> true := fun (p : s = false) (q : s = true) => false_not_true (eq_trans' p q).
        (* eq_ind_r (fun s : bool => s <> true) false_not_true (y := s) *)

    Definition Pimptobimp : (s=true -> t=true) -> (s→t)=true :=  bool_ind (fun b : bool => (b = true -> t = true) -> (b→t) = true)
        (fun f : true = true -> t = true => f eq_refl) (fun _ : false = true -> t = true => eq_refl) s.

    Definition bmopo : (s→t) = true -> s = true -> t = true := fun (f : (s→t) = true) (x : s = true) =>
        eq_trans' (f_equal (fun b : bool => b→t) x) f.
        (* eq_ind_r (fun b : bool => (b→t) = true -> t = true) (fun g : (true→t) = true => g) x f. *)

    Definition onefthenbandf : s = false \/ t = false -> (s && t) = false := or_ind (f_equal (fun b : bool => b && t) (y := false))
        (fun q : t = false => eq_trans (f_equal (andb s) q) (bool_ind (fun b : bool => (b && false) = false) eq_refl eq_refl s)).
        (* or_ind (eq_ind_r (x := false) (fun b : bool => (b∧t) = false) eq_refl (y := s))
        (eq_ind_r (fun c : bool => (s∧c) = false) (bool_ind (fun b : bool => (b∧false) = false) eq_refl eq_refl s) (y := t)) *)

    Definition nteqf : forall {s : bool}, ¬s = true  -> s = false :=
        bool_ind (fun s : bool => ¬s = true  -> s = false) (eq_sym (y := _)) (f_equal negb (y := _)).

    Definition nfeqt : forall {s : bool}, ¬s = false -> s = true  :=
        bool_ind (fun s : bool => ¬s = false -> s = true ) (f_equal negb (y := _)) (eq_sym (y := _)).

    Definition bcomp : forall s : bool, (s && ¬s) = false := bool_ind (fun s : bool => (s && ¬s) = false) eq_refl eq_refl.

    Definition bool_class : forall s : bool, (s || ¬s) = true := bool_ind (fun s : bool => (s || ¬s) = true) eq_refl eq_refl.

    Definition bclassP  : forall b : bool, b = true \/ b = false
        := bool_ind (fun b : bool => b = true \/ b = false) (or_introl eq_refl) (or_intror eq_refl).

    (* Ok, so not a boolean axiom, but still nice! Basically defining f+g in a category with coproducts *)
    Definition sum_arr : forall {A B C D : Prop}, (A -> C) -> (B -> D) -> (A \/ B) -> (C \/ D)
        := fun (A B C D : Prop) (f : A -> C) (g : B -> D) => or_ind (fun x : A => or_introl (f x)) (fun y : B => or_intror (g y)).
End Bool_theorems.

(* TODO: Can I just write these as Theorems and leave it at that? *)
(* possibly need to use Hint's? *)
Section Prop_pre_bool_alg.
    Variables (R : prop -> prop) (p q r : prop).

    Definition entail_refl  : p entails p := fun (w : world) (e : (tv p w) = true) => e.

    Definition entail_trans : (p entails q) -> (q entails r) -> (p entails r)
        := fun (f : p entails q) (g : q entails r) (w : world) (e : (tv p w) = true) => g w (f w e).

    Definition p_and_e1 : (p and q) entails p :=
        fun (w : world) (e : (tv (p and q) w) = true) => bande1 (tv p w) (tv q w) (eq_trans' (p_and_ax p q w) e).

    Definition p_and_e2 : (p and q) entails q :=
        fun (w : world) (e : (tv (p and q) w) = true) => bande2 (tv p w) (tv q w) (eq_trans' (p_and_ax p q w) e).

    Definition p_and_i (f : r entails p) (g : r entails q) : r entails (p and q) := fun (w : world) (e : (tv r w) = true) =>
        eq_trans (p_and_ax p q w) (bandi (tv p w) (tv q w) (f w e) (g w e)).

    Definition p_or_e (f : p entails r) (g : q entails r) : (p or q) entails r := fun (w : world) (e : (tv (p or q) w) = true) =>
        boreind (tv p w) (tv q w) (tv r w) (eq_trans' (p_or_ax p q w) e) (f w) (g w).

    Definition p_or_i1 : p entails (p or q) := fun (w : world) (e : (tv p w) = true) =>
        eq_trans (p_or_ax p q w) (bori1 (tv p w) (tv q w) e).

    Definition p_or_i2 : q entails (p or q) := fun (w : world) (e : (tv q w) = true) =>
        eq_trans (p_or_ax p q w) (bori2 (tv p w) (tv q w) e).

    Definition truth_top    : p entails truth   := fun (w : world) (_ : (tv p w) = true) => truth_ax w.

    Definition falsity_bot  : falsity entails p := fun (w : world) (e : (tv falsity w) = true) =>
        False_ind ((tv p w) = true) (boolcantbeboth (tv falsity w) (falsity_ax w) e).

    Definition residual_law1 (f : (p and q) entails r) : p entails (q implies r) :=
        fun (w : world) (e : (tv p w) = true) => eq_trans (p_implies_ax q r w)
            (Pimptobimp (tv q w) (tv r w) (fun x : (tv q w) = true => f w (eq_trans (p_and_ax p q w) (bandi (tv p w) (tv q w) e x)))).

    Definition residual_law2 (g : p entails (q implies r)) : (p and q) entails r := fun (w : world) (e : (tv (p and q) w) = true) =>
        bmopo (tv q w) (tv r w) (eq_trans' (p_implies_ax q r w) (g w (p_and_e1 w e))) (p_and_e2 w e).

    Definition complement : forall w : world, (tv (p and (not p)) w) = false := fun (w : world) =>
        eq_trans (eq_trans (p_and_ax p (p_not p) w) (f_equal (andb (tv p w)) (p_not_ax p w))) (bcomp (tv p w)).

    Definition lem : forall w : world, (tv (p or (not p)) w) = true := fun (w : world) =>
        eq_trans (eq_trans (p_or_ax p (not p) w) (f_equal (orb (tv p w)) (p_not_ax p w))) (bool_class (tv p w)).

    Definition dne : (not (not p)) entails p := fun (w : world) (e : tv (not (not p)) w = true) =>
        nfeqt (eq_trans' (p_not_ax p w) (nteqf (eq_trans' (p_not_ax (not p) w) e))).

    Definition p_forall_e : (p_forall R) entails (R p) := fun (w : world) (e : tv (p_forall R) w = true) =>
        proj1 (p_forall_ax R w) e p.

    Definition p_forall_i : (forall p : prop, q entails (R p)) -> q entails (p_forall R)
        := fun (f : forall p : prop, q entails (R p)) (w : world) (e : (tv q w) = true) =>
            proj2 (p_forall_ax R w) (fun p : prop => f p w e).

    Definition p_exists_i : (R p) entails (p_exists R) := fun (w : world) (e : (tv (R p) w) = true) =>
        proj2 (p_exists_ax R w) (ex_intro (fun q : prop => (tv (R q) w) = true) p e).

    Definition p_exists_e : (forall p : prop, (R p) entails q) -> (p_exists R) entails q :=
        fun (f : forall p : prop, (R p) entails q) (w : world) (e : (tv (p_exists R) w) = true) =>
            ex_ind (fun (p : prop) => f p w) (proj1 (p_exists_ax R w) e).

    (* The following axioms requires that world is inhabited, specifically by a term w₀ *)

    Definition nondeg : ~(truth ≡ falsity)
        := and_ind (fun (f : truth entails falsity) _ => boolcantbeboth (tv falsity w₀) (falsity_ax w₀) (f w₀ (truth_ax w₀))).
        (* fun e:truth ≡ falsity => match e with conj f _ => boolcantbeboth (tv falsity w₀) (falsity_ax w₀) (f w₀ (truth_ax w₀))end *)

    (* (in)equality at w₀ means (in)equality everywhere *)
    Definition eqw0eqev : (tv (p equals q) w₀) = true -> forall u : world, (tv (p equals q) u) = true
        := fun (e : (tv (p equals q) w₀) = true) (u : world) => proj2 (p_equals_ax p q u) (proj1 (p_equals_ax p q w₀) e).
    Definition neqw0neqev : (tv (p equals q) w₀) = false -> forall v : world, (tv (p equals q) v) <> true
        := fun (n : (tv (p equals q) w₀) = false) (v : world) (m : (tv (p equals q) v) = true) =>
            boolcantbeboth (tv (p equals q) w₀) n (proj2 (p_equals_ax p q w₀) (proj1 (p_equals_ax p q v) m)).
End Prop_pre_bool_alg.

(* The following axioms require that w is inhabited *)

Definition eq_one : forall p q : prop, ((p equals q) ≡ truth) \/ ((p equals q) ≡ falsity) := fun p q : prop =>
    sum_arr (fun e : (tv (p equals q) w₀) = true  => conj   (truth_top (p equals q))
                                                            (fun (u : world) (_ : (tv truth u) = true) => eqw0eqev p q e u))
            (fun n : (tv (p equals q) w₀) = false => conj   (fun (v : world) (m : (tv (p equals q) v) = true) =>
                                                                False_ind ((tv falsity v) = true) (neqw0neqev p q n v m))
                                                            (falsity_bot (p equals q)))
            (bclassP (tv (p equals q) w₀)).
    (* Definition eq_one : forall p q : prop, (p equals q) ≡ truth \/ (p equals q) ≡ falsity := fun p q : prop =>
        sum_arr (fun x : (tv (p equals q) w₀) = true => conj (truth_top (p equals q))
                    (fun (w : world) (_ : (tv truth w) = true) => proj2 (p_equals_ax p q w) (proj1 (p_equals_ax p q w₀) x)))
                (fun y : (tv (p equals q) w₀) = false => conj (fun (w : world) (d : (tv (p equals q) w) = true) =>
                    match (match (proj2 (p_equals_ax p q w₀) (proj1 (p_equals_ax p q w) d)) in (_ = v)
                        return (v = false) with eq_refl => y end)
                    in (_ = z) return (if z then True else ((tv falsity w) = true)) with eq_refl => I end)
                (falsity_bot (p equals q))) (bclassP (tv (p equals q) w₀)). *)

Definition eq_two : forall p q : prop, (p equals q) ≡ truth <-> p = q := fun p q : prop => conj
    (fun u : (p equals q) ≡ truth =>    match u with conj _ f => proj1 (p_equals_ax p q w₀) (f w₀ (truth_ax w₀)) end)
    (fun e : p = q => conj (truth_top (p equals q)) (fun (w : world) (_ : (tv truth w) = true) => proj2 (p_equals_ax p q w) e)).

(* Definition eq_one_weak : forall p q : prop, p = q \/ p <> q -> (p equals q) ≡ truth \/ (p equals q) ≡ falsity
    := fun (p q : prop) (o : p = q \/ p <> q) =>
            match o with
                | or_introl e => or_introl (conj    (truth_top (p equals q))
                                                    (fun (w : world) (_ : (tv truth w) = true) => proj2 (p_equals_ax p q w) e))
                | or_intror n => or_intror (conj    (fun (w : world) (e : (tv (p equals q) w) = true) =>
                                                        False_ind ((tv falsity w) = true) (n (proj1 (p_equals_ax p q w) e)))
                                                    (falsity_bot (p equals q)))
            end. *)

Definition all_worlds_ultra : forall w : world, ultrafilter (facts w) :=
    fun w : world =>
     conj   (fun (p q : prop) (e : (tv p w) = true) (f : p entails q) => f w e)
    (conj   (fun (p q : prop) (u : (tv p w) = true) (v : (tv q w) = true) => eq_trans (p_and_ax p q w) (f_equal2 andb u v))
    (conj   (fun p : prop => sum_arr (fun e => e) (eq_trans (p_not_ax p w))
                    (if (tv p w) as s return s = true \/ ¬s = true then or_introl eq_refl else or_intror eq_refl))
            (falsity_ax w))).

(* John Bell "boolean algebras, constructively" *)
(* stone algebras- btw Heyting and Boolean algebras *)
    (* all deMorgan laws valid *)
Definition wkr_thm : forall p q : prop, (exists s : pset, (((s p) = true) /\ ((s q) = false)) /\ (ultrafilter s))
    -> (exists w : world, ((tv p w) = true) /\ ((tv q w) = false))
    := fun p q : prop =>
        ex_ind (fun s : pset => and_ind (fun (b : ((s p) = true) /\ ((s q) = false)) (ult : (ultrafilter s)) =>
            ex_ind (fun (w : world) (e : s = (facts w)) => ex_intro (fun u : world => ((tv p u) = true) /\ ((tv q u) = false)) w
              (eq_ind s (fun t : pset => ((t p) = true) /\ ((t q) = false)) b (facts w) e)) (all_ultras_worlds s ult))).

(* Prove: ⊢∀p,q:p.[~ (p entails q) -> ∃w:w.[p@w = true /\ q@w = false]] *)

(* TODO: make statterm arg implicit? *)
Definition ext_at : forall s : statterm, (Sns s) -> world -> (Ext s) :=
    statterm_rec (fun s : statterm => (Sns s) -> world -> (Ext s)) (fun x _ => x) tv (fun s _ t g f w x => g (f x) w).

(* Fixpoint ext_at2 (s : statterm) : (Sns s) -> world -> (Ext s) :=
    match s as t return ((Sns t) -> world -> (Ext t)) with
        | ent       => fun x _ => x
        | prp       => tv
        | func a b  => fun f w x => ext_at2 b (f x) w
    end. *)
