(* extensions- (hopefully) the final version of worlds_prim/entails_def *)

Load CDS_prims.

Module entails_def.
    Definition p_entails := fun p q : prop => forall w : world, (p@w) = true -> (q@w) = true.
End entails_def.

Module Import Ultra := Ult entails_def.

Section prop_axioms.
    Axiom p_and_ax      : forall (p q : prop) (w : world), ((p and q)@w) = ((p@w) && (q@w)).
    Axiom p_or_ax       : forall (p q : prop) (w : world), ((p or q)@w) = ((p@w) || (q@w)).
    Axiom p_implies_ax  : forall (p q : prop) (w : world), ((p implies q)@w) = ((p@w) ~> (q@w)).
    Axiom p_iff_ax      : forall (p q : prop) (w : world), ((p iff q)@w) = (((p implies q)@w) && ((q implies p)@w)).
    Axiom p_not_ax      : forall (p   : prop) (w : world), ((not p)@w) = -~(p@w).
    Axiom truth_ax      : forall w : world, (truth@w)   = true.
    Axiom falsity_ax    : forall w : world, (falsity@w) = false.
    Axiom p_equals_ax   : forall (s : statterm) (x y : (Sns s)) (w : world), (((p_equals s x y)@w) = true) <-> (x = y).
    Axiom p_exists_ax   : forall (s : statterm) (R : (Sns s) -> prop) (w : world),
        (((p_exists s R)@w) = true) <-> ~(forall x : (Sns s), ((R x)@w) = false).
    Axiom p_forall_ax   : forall (s : statterm) (R : (Sns s) -> prop) (w : world),
        (((p_forall s R)@w) = true) <-> (forall x : (Sns s), ((R x)@w) = true).
End prop_axioms.

Section Useful_lemmas.
    Definition eq_trans' : forall {A : Type} {x y z : A}, x = y -> x = z -> y = z
        := fun (A : Type) (x y z : A) (u : x = y) (v : x = z) => match u in (_ = a) return (a = z) with eq_refl => v end.

    Definition tnf : true <> false := eq_ind true (fun b : bool => if b then True else False) I false.
End Useful_lemmas.

Section prop_Theorems.
    Definition facts_ultra  : forall w : world, ultrafilter (facts w)
        :=   fun w : world =>
             conj   (fun (p q : prop) (e : (p@w) = true) (f : p entails q) => f w e)
            (conj   (fun (p q : prop) (u : (p@w) = true) (v : (q@w) = true) => eq_trans (p_and_ax p q w) (f_equal2 andb u v))
            (conj   (fun p : prop => (if (p@w) as b return ((p@w) = b -> ((p@w) = true) \/ (((not p)@w) = true))
                                      then (fun u : (p@w) = true => or_introl u)
                                      else (fun v : (p@w) = false => or_intror (eq_trans (p_not_ax p w) (f_equal negb v))))
                                    eq_refl)
                    (falsity_ax w))).

    Definition entail_refl  : forall p : prop, p entails p
        := fun (p : prop) (w : world) (e : (p@w) = true) => e.

    Definition entail_trans : forall p q r : prop, (p entails q) -> (q entails r) -> (p entails r)
        := fun (p q r : prop) (f : p entails q) (g : q entails r) (w : world) (e : (p@w) = true) => g w (f w e).

    Definition p_and_e1     : forall p q : prop, (p and q) entails p
        :=  fun (p q : prop) (w : world) (e : ((p and q)@w) = true) =>
            (if (p@w) as b return ((b && (q@w)) = true -> b = true)
             then (fun u : (q@w) = true => eq_refl)
             else (fun v : false = true => v))
            (eq_trans' (p_and_ax p q w) e).

    Definition p_and_e2     : forall p q : prop, (p and q) entails q
        :=  fun (p q : prop) (w : world) (e : ((p and q)@w) = true) =>
            (if (p@w) as b return ((b && (q@w)) = true -> (q@w) = true)
             then (fun u : (q@w) = true => u)
             else (fun v : false = true => if (q@w) as c return (c = true) then eq_refl else v))
            (eq_trans' (p_and_ax p q w) e).

    Definition p_and_i      : forall p q r : prop, p entails q -> p entails r -> p entails (q and r)
        :=  fun (p q r : prop) (f : p entails q) (g : p entails r) (w : world) (e : (p@w) = true) =>
            eq_trans (p_and_ax q r w) (f_equal2 andb (f w e) (g w e)).

    Definition p_or_e       : forall p q r : prop, p entails r -> q entails r -> (p or q) entails r
        :=  fun (p q r : prop) (f : p entails r) (g : q entails r) (w : world) (e : ((p or q)@w) = true) =>
            (if (p@w) as b return ((p@w) = b -> (b || (q@w)) = true -> (r@w) = true)
              then (fun (u : (p@w) = true) (v : true = true) => f w u)
              else (fun x : (p@w) = false => g w))
            eq_refl
            (eq_trans' (p_or_ax p q w) e).

    Definition p_or_i1      : forall p q : prop, p entails (p or q)
        := fun (p q : prop) (w : world) (e : (p@w) = true) => eq_trans (p_or_ax p q w) (f_equal (fun b : bool => b || (q@w)) e).

    Definition p_or_i2      : forall p q : prop, q entails (p or q)
        :=  fun (p q : prop) (w : world) (e : (q@w) = true) =>
            eq_trans (p_or_ax p q w) (if (p@w) as b return ((b || (q@w)) = true) then eq_refl else e).

    Definition truth_top    : forall p : prop, p entails truth
        := fun (p : prop) (w : world) (e : (p@w) = true) => truth_ax w.

    Definition falsity_bot  : forall p : prop, falsity entails p
        :=  fun (p : prop) (w : world) (e : (falsity@w) = true) =>
            if (p@w) as b return (b = true) then eq_refl else (eq_trans' (falsity_ax w) e).

    Definition p_implies_i  : forall p q r : prop, (p and q) entails r -> p entails (q implies r)
        :=  fun (p q r : prop) (f : (p and q) entails r) (w : world) (e : (p@w) = true) =>
            eq_trans    (p_implies_ax q r w)
                        ((if (q@w) as c return ((q@w) = c -> (c ~> (r@w)) = true)
                         then (fun u : (q@w) = true => f w (eq_trans (p_and_ax p q w) (f_equal2 andb e u)))
                         else (fun v : (q@w) = false => eq_refl))
                         eq_refl).

    Definition p_implies_e  : forall p q : prop, (p and (p implies q)) entails q
        :=  fun (p q : prop) (w : world) (e : ((p and (p implies q))@w) = true) =>
            eq_trans'   (eq_trans (p_implies_ax p q w) (f_equal (fun b : bool => b ~> (q@w)) (p_and_e1 p (p implies q) w e)))
                        (p_and_e2 p (p implies q) w e).

    Definition complement : forall (p : prop) (w : world), ((p and (not p))@w) = false
        :=  fun (p : prop) (w : world) =>
            eq_trans    (eq_trans (p_and_ax p (not p) w) (f_equal (andb (p@w)) (p_not_ax p w)))
                        (if (p@w) as b return ((b && -~b) = false) then eq_refl else eq_refl).

    Definition lem : forall (p : prop) (w : world), ((p or (not p))@w) = true
        :=  fun (p : prop) (w : world) =>
            eq_trans    (eq_trans (p_or_ax p (not p) w) (f_equal (orb (p@w)) (p_not_ax p w)))
                        (if (p@w) as b return ((b || -~b) = true) then eq_refl else eq_refl).

    Definition dne : forall p : prop, (not (not p)) entails p
        :=  fun (p : prop) (w : world) (e : ((not (not p))@w) = true) =>
            (if (p@w) as b return (-~(-~b) = true -> b = true) then (fun u : true = true => u) else (fun v : false = true => v))
            (eq_trans' (eq_trans (p_not_ax (not p) w) (f_equal negb (p_not_ax p w))) e).

    Definition p_forall_e : forall (s : statterm) (R : (Sns s) -> prop) (x : (Sns s)), (p_forall s R) entails (R x)
        :=  fun (s : statterm) (R : (Sns s) -> prop) (x : (Sns s)) (w : world) (e : ((p_forall s R)@w) = true) =>
            proj1 (p_forall_ax s R w) e x.

    Definition p_forall_i : forall (s : statterm) (R : (Sns s) -> prop) (p : prop),
                                (forall x : (Sns s), p entails (R x)) -> p entails (p_forall s R)
        :=  fun (s : statterm) (R : (Sns s) -> prop) (p : prop)
                (f : forall x : (Sns s), p entails (R x)) (w : world) (e : (p@w) = true) =>
            proj2 (p_forall_ax s R w) (fun x : (Sns s) => f x w e).

    Definition p_exists_e : forall (s : statterm) (R : (Sns s) -> prop) (p : prop),
                                (forall x : (Sns s), (R x) entails p) -> (p_exists s R) entails p
        :=  fun (s : statterm) (R : (Sns s) -> prop) (p : prop)
                (g : forall x : (Sns s), (R x) entails p) (w : world) (e : ((p_exists s R)@w) = true) =>
            (if (p@w) as b return ((p@w) = b -> (p@w) = true)
             then (fun c : (p@w) = true => c)
             else (fun d : (p@w) = false =>
                    False_ind ((p@w) = true)
                        (proj1 (p_exists_ax s R w) e
                            (fun x : (Sns s) =>
                                (if ((R x)@w) as t return (((R x)@w) = t -> ((R x)@w) = false)
                                 then (fun y : ((R x)@w) = true => False_ind (((R x)@w) = false) (tnf (eq_trans' (g x w y) d)))
                                 else (fun z : ((R x)@w) = false => z))
                                eq_refl))))
            eq_refl.

    Definition p_exists_i : forall (s : statterm) (R : (Sns s) -> prop) (x : (Sns s)), (R x) entails (p_exists s R)
        :=  fun (s : statterm) (R : (Sns s) -> prop) (x : (Sns s)) (w : world) (e : ((R x)@w) = true) =>
            proj2 (p_exists_ax s R w) (fun f : forall y : (Sns s), ((R y)@w) = false => tnf (eq_trans' e (f x))).

    (* generalized version of eqw0eqev/neqw0neqev (doesn't require world to be inhabited) *)
    Definition eqiseqev : forall (s : statterm) (x y : (Sns s)) (u v : world), ((p_equals s x y)@u) = ((p_equals s x y)@v)
        :=  fun (s : statterm) (x y : (Sns s)) (u v : world) =>
            (if ((p_equals s x y)@v) as t return (((p_equals s x y)@v) = t -> ((p_equals s x y)@u) = t)
             then (fun c : ((p_equals s x y)@v) = true => proj2 (p_equals_ax s x y u) (proj1 (p_equals_ax s x y v) c))
             else (fun d : ((p_equals s x y)@v) = false =>
                    (if ((p_equals s x y)@u) as b return (((p_equals s x y)@u) = b -> b = false)
                     then (fun a : ((p_equals s x y)@u) = true =>
                            eq_trans' (proj2 (p_equals_ax s x y v) (proj1 (p_equals_ax s x y u) a)) d)
                     else (fun e : ((p_equals s x y)@u) = false => eq_refl))
                    eq_refl))
            eq_refl.

    (* These last 3 axioms requires that world is inhabited, specifically by a term w0 *)

    Definition nondeg : ~(truth ≡ falsity)
        := and_ind (fun (f : truth entails falsity) (g : falsity entails truth) =>
                        tnf (eq_trans' (f w0 (truth_ax w0)) (falsity_ax w0))).

    Definition eq_one : forall (s : statterm) (x y : (Sns s)), ((p_equals s x y) ≡ truth) \/ ((p_equals s x y) ≡ falsity)
        :=  fun (s : statterm) (x y : (Sns s)) =>
            (if ((p_equals s x y)@w0) as b
             return (((p_equals s x y)@w0) = b -> ((p_equals s x y) ≡ truth) \/ ((p_equals s x y) ≡ falsity))
             then (fun c : ((p_equals s x y)@w0) = true =>
                    or_introl   (conj   (truth_top (p_equals s x y))
                                        (fun (v : world) (e : (truth@v) = true) => eq_trans' (eqiseqev s x y w0 v) c)))
             else (fun d : ((p_equals s x y)@w0) = false =>
                    or_intror   (conj   (fun (v : world) (e : ((p_equals s x y)@v) = true) =>
                                            if (falsity@v) as t return (t = true)
                                            then eq_refl
                                            else (eq_trans' d (eq_trans (eqiseqev s x y w0 v) e)))
                                        (falsity_bot (p_equals s x y)))))
            eq_refl.

    Definition eq_two : forall (s : statterm) (x y : (Sns s)), ((p_equals s x y) ≡ truth) <-> (x = y)
        :=  fun (s : statterm) (x y : (Sns s)) =>
            conj    (and_ind (fun (f : (p_equals s x y) entails truth) (g : truth entails (p_equals s x y)) =>
                                proj1 (p_equals_ax s x y w0) (g w0 (truth_ax w0))))
                    (fun e : x = y => conj  (truth_top (p_equals s x y))
                                            (fun (u : world) (c : (truth@u) = true) => proj2 (p_equals_ax s x y u) e)).
End prop_Theorems.

(* basically showing that ≡_p implies mutual entailment *)
Definition int_eq : forall p q : prop, (forall w : world, (p@w) = (q@w)) -> p ≡ q
    :=  fun (p q : prop) (f : forall w : world, (p @ w) = (q @ w)) =>
        conj (fun w : world => eq_trans' (f w)) (fun w : world => eq_trans (f w)).

(* duality of prop quantifiers *)
Definition comp : forall {A B C:Type},(B->C)->(A->B)->A->C := fun (A B C : Type) (f : B -> C) (g : A -> B) (x : A) => f (g x).
Infix "∘" := comp (at level 20).
Definition dubneg : forall b : bool, b = -~(-~b) := bool_ind (fun b : bool => b = -~(-~b)) eq_refl eq_refl.

Section QuantifierDuals.
    Hypotheses (s : statterm) (P : Sns s -> prop).
    Definition qudupr1 : (p_exists s P) ≡ (not (p_forall s (p_not∘P)))
        :=  conj    (fun (w : world) (d : ((p_exists s P)@w) = true) =>
                        eq_trans (p_not_ax (p_forall s (p_not∘P)) w)
                            (f_equal negb
                                ((if ((p_forall s (p_not∘P))@w) as b return (((p_forall s (p_not∘P))@w) = b -> b = false)
                                  then  (fun e : ((p_forall s (p_not∘P))@w) = true =>
                                            False_ind (true = false)
                                                (proj1  (p_exists_ax s P w) d
                                                        (fun x : Sns s =>
                                                            eq_trans    (dubneg ((P x)@w))
                                                                        (f_equal negb
                                                                            (eq_trans' (p_not_ax (P x) w)
                                                                                (proj1 (p_forall_ax s (p_not∘P) w) e x))))))
                                  else  (fun _ : ((p_forall s (p_not∘P))@w) = false => eq_refl))
                                 eq_refl)))
                    (fun (w : world) (d : (((not p_forall s (p_not∘P)))@w) = true) =>
                        proj2   (p_exists_ax s P w)
                                (fun f : forall x : Sns s, (P x @ w) = false =>
                                    tnf (eq_trans'
                                            (proj2 (p_forall_ax s (p_not∘P) w)
                                                (fun x : Sns s => eq_trans (p_not_ax (P x) w) (f_equal negb (f x))))
                                            (eq_trans (dubneg ((p_forall s (p_not∘P))@w))
                                                (f_equal negb (eq_trans' (p_not_ax (p_forall s (p_not∘P)) w) d)))))).
    Definition qudupr2 : (p_forall s P) ≡ (not (p_exists s (p_not∘P)))
        :=  conj    (fun (w : world) (d : ((p_forall s P)@w) = true) =>
                        eq_trans (p_not_ax (p_exists s (p_not∘P)) w)
                            (f_equal negb
                                ((if ((p_exists s (p_not∘P))@w) as b return ((p_exists s (p_not ∘ P) @ w) = b -> b = false)
                                  then (fun e : ((p_exists s (p_not∘P))@w) = true =>
                                            False_ind (true = false)
                                                (proj1  (p_exists_ax s (p_not∘P) w) e
                                                        (fun x : Sns s =>
                                                            eq_trans (p_not_ax (P x) w)
                                                                (f_equal negb (proj1 (p_forall_ax s P w) d x)))))
                                  else (fun _ : ((p_exists s (p_not∘P))@w) = false => eq_refl))
                                 eq_refl)))
                    (fun (w : world) (d : ((not (p_exists s (p_not∘P)))@w) = true) =>
                        proj2   (p_forall_ax s P w)
                                (fun x : Sns s =>
                                    (if ((P x)@w) as b return (((P x)@w) = b -> b = true)
                                     then   (fun _ : (P x @ w) = true => eq_refl)
                                     else   (fun e : (P x @ w) = false =>
                                                eq_trans'
                                                    (eq_trans   (dubneg ((p_exists s (p_not∘P))@w))
                                                                (f_equal negb (eq_trans' (p_not_ax (p_exists s (p_not∘P)) w) d)))
                                                    (proj2 (p_exists_ax s (p_not∘P) w)
                                                         (fun f : forall y : Sns s, ((not (P y))@w) = false =>
                                                          tnf (eq_trans'    (eq_trans (p_not_ax (P x) w) (f_equal negb e))
                                                                            (f x))))))
                                    eq_refl)).
    Definition qudupr3 : (p_exists s (p_not∘P)) ≡ (not (p_forall s P))
        :=  conj    (fun (w : world) (d : ((p_exists s (p_not∘P))@w) = true) =>
                        eq_trans (p_not_ax (p_forall s P) w)
                            (f_equal negb
                                ((if ((p_forall s P)@w) as b return (((p_forall s P)@w) = b -> b = false)
                                  then  (fun e : (p_forall s P @ w) = true =>
                                            False_ind (true = false)
                                                (proj1 (p_exists_ax s (p_not∘P) w) d
                                                    (fun x : Sns s =>
                                                        eq_trans (p_not_ax (P x) w)
                                                            (f_equal negb (proj1 (p_forall_ax s P w) e x)))))
                                  else  (fun _ : ((p_forall s P)@w) = false => eq_refl))
                                 eq_refl)))
                    (fun (w : world) (d : ((not (p_forall s P))@w) = true) =>
                        proj2 (p_exists_ax s (p_not∘P) w)
                            (fun f : forall x : Sns s, ((p_not∘P) x @ w) = false =>
                                tnf (eq_trans'
                                        (proj2 (p_forall_ax s P w)
                                            (fun x : Sns s =>
                                                eq_trans    (dubneg ((P x)@w))
                                                            (f_equal negb (eq_trans' (p_not_ax (P x) w) (f x)))))
                                        (eq_trans   (dubneg ((p_forall s P)@w))
                                                    (f_equal negb (eq_trans' (p_not_ax (p_forall s P) w) d)))))).
    Definition qudupr4 : (p_forall s (p_not∘P)) ≡ (not (p_exists s P))
        := conj     (fun (w : world) (d : ((p_forall s (p_not∘P))@w) = true) =>
                        eq_trans (p_not_ax (p_exists s P) w)
                            (f_equal negb
                                ((if ((p_exists s P)@w) as b return (((p_exists s P)@w) = b -> b = false)
                                  then  (fun e : ((p_exists s P)@w) = true =>
                                            False_ind (true = false)
                                                (proj1 (p_exists_ax s P w) e
                                                    (fun x : Sns s =>
                                                        eq_trans (dubneg ((P x)@w))
                                                            (f_equal negb
                                                                (eq_trans'  (p_not_ax (P x) w)
                                                                            (proj1 (p_forall_ax s (p_not∘P) w) d x))))))
                                  else  (fun _ : ((p_exists s P)@w) = false => eq_refl))
                                 eq_refl)))
                    (fun (w : world) (d : ((not (p_exists s P))@w) = true) =>
                        proj2 (p_forall_ax s (p_not∘P) w)
                            (fun x : Sns s =>
                              eq_trans  (p_not_ax (P x) w)
                                        (f_equal negb
                                            ((if ((P x)@w) as b return (((P x)@w) = b -> b = false)
                                              then
                                              (fun e : ((P x)@w) = true =>
                                                eq_trans'   (proj2 (p_exists_ax s P w)
                                                                (fun f : forall y : Sns s, ((P y)@w) = false =>
                                                                    tnf (eq_trans' e (f x))))
                                                            (eq_trans   (dubneg ((p_exists s P)@w))
                                                                        (f_equal negb
                                                                            (eq_trans' (p_not_ax (p_exists s P) w) d))))
                                              else  (fun _ : ((P x)@w) = false => eq_refl))
                                             eq_refl)))).
End     QuantifierDuals.




