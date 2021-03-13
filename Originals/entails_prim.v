(* entails_prim *)

Load CDS_primitives.
Open Scope sem_scope.

Axiom p_entails : prop -> prop -> Prop.
Infix "entails" := p_entails (at level 50) : sem_scope.
Definition p_equiv : prop -> prop -> Prop := fun p q : prop => (p entails q) /\ (q entails p).
Infix "≡" := p_equiv (at level 40) : sem_scope.

(* TODO: axiomatize this s.t. we entails, which will be a preorder, s.t. the propositional connectives form a boolean algebra *)
(* is everything in Preboolean_Axioms enough? *)
Section Preboolean_Axioms.
    (* "entails" is a preorder *)
    Axiom entail_refl   : forall p : prop, p entails p.
    Axiom entail_trans  : forall p q r : prop, (p entails q) -> (q entails r) -> (p entails r).

    (* "and" is a glb *)
    Axiom p_and_e1  : forall p q : prop, (p and q) entails p.
    Axiom p_and_e2  : forall p q : prop, (p and q) entails q.
    Axiom p_and_i   : forall p q r : prop, (p entails q) -> (p entails r) -> (p entails (q and r)).

    (* "or" is an lub *)
    Axiom p_or_e    : forall p q r : prop, (p entails r) -> (q entails r) -> ((p or q) entails r).
    Axiom p_or_i1   : forall p q : prop, p entails (p or q).
    Axiom p_or_i2   : forall p q : prop, q entails (p or q).

    (* "truth" and "falsity" are top and bottom, respectively *)
    Axiom truth_top     : forall p : prop, p entails truth.
    Axiom falsity_bot   : forall p : prop, falsity entails p.

    (* "implies" is a residual operator *)
    Axiom residual_law1 : forall p q r : prop, ((p and q) entails r) -> (p entails (q implies r)).
    Axiom residual_law2 : forall p q r : prop, (p entails (q implies r)) -> ((p and q) entails r).

    (* "iff" is bi-implication *)
    Axiom p_iff_e1  : forall p q : prop, (p iff q) entails (p implies q).
    Axiom p_iff_e2  : forall p q : prop, (p iff q) entails (q implies p).
    Axiom p_iff_i   : forall p q : prop, ((p implies q) and (q implies p)) entails (p iff q).

    (* "p_not" is complement *)
    Axiom p_not_comp    : forall p : prop, (p and (not p)) entails falsity. (* thus, provably, (not p) entails (p implies falsity) *)
    Axiom pif_p_not_p   : forall p : prop, (p implies falsity) entails (not p).
        (* can't actually prove this w/ everything else (as best I could tell) *)
    Axiom dne           : forall  : prop, (not (not p)) entails p.

    (* Quantifiers (for prop's only) TODO: generalize quantifiers over sense types *)
    Axiom p_forall_e    : forall (R : prop -> prop) (p : prop), (p_forall R) entails (R p).
    Axiom p_forall_i    : forall (R : prop -> prop) (p : prop), (forall q : prop, p entails (R q)) -> (p entails (p_forall R)).
    Axiom p_exists_e    : forall (R : prop -> prop) (p : prop), (forall q : prop, (R q) entails p) -> ((p_exists R) entails p).
    Axiom p_exists_i    : forall (R : prop -> prop) (p : prop), (R p) entails (p_exists R).

    (* non-degeneracy *)
    Axiom nondeg        : ~(truth entails falsity).
        (* no point in making it ~(truth ≡ falsity) since we already have 2 proofs of (falsity entails truth), don't need a third! *)

    (* equality axioms (for prop's only) TODO: generalize quantifiers over sense types *)
    (* does one of these follow from the other? *)
    Axiom eq_one    : forall p q : prop, ((p equals q) ≡ truth) \/ ((p equals q) ≡ falsity).
        (* for similar reasons as in nondeg, may just change this to (truth entails (p equals q)) \/ ((p equals q) entails falsity) *)
    Axiom eq_two    : forall p q : prop, ((p equals q) ≡ truth) <-> (p = q).
End Preboolean_Axioms.

(* Move into CDS_primitives? *)
Definition pset : Set := prop -> bool.
Section Ultra.
    Variable s : pset.

    Definition uc  : pset -> Prop := fun s : pset => forall p q : prop, ((s p) = true) -> (p entails q) -> ((s q) = true).
    Definition ac  : pset -> Prop := fun s : pset => forall p q : prop, ((s p) = true) -> ((s q) = true) -> ((s (p and q)) = true).
    Definition sai : pset -> Prop := fun s : pset => forall p   : prop, ((s p) = true) \/ ((s (not p)) = true).
    Definition cst : pset -> Prop := fun s : pset => (s falsity) = false.
    Definition ultrafilter : pset -> Prop := fun s : pset => (uc s) /\ (ac s) /\ (sai s) /\ (cst s).
        (* for the record, "/\" associates to the right, so this comes out as (uc s) /\ ((ac s) /\ ((sai s) /\ (cst s))) *)
End Ultra.
(* define world as the type of ultrafilters on props *)
Definition world : Set := {s : pset | ultrafilter s}.
Definition tv : prop -> world -> bool := fun (p : prop) (w : world) => proj1_sig w p.
Definition facts : world -> pset := fun w : world => proj1_sig w.
(* mappings from each world to each of the parts of the proof it is an ultrafilter *)
Definition upcl     : forall w : world, uc  (facts w)
    := sig_ind (fun w : world => uc  (facts w)) (fun (s : pset) (u : ultrafilter s) => proj1 u).
Definition ancl     : forall w : world, ac  (facts w)
    := sig_ind (fun w : world => ac  (facts w)) (fun (s : pset) (u : ultrafilter s) => proj1 (proj2 u)).
Definition stalis   : forall w : world, sai (facts w)
    := sig_ind (fun w : world => sai (facts w)) (fun (s : pset) (u : ultrafilter s) => proj1 (proj2 (proj2 u))).
Definition consist  : forall w : world, cst (facts w)
    := sig_ind (fun w : world => cst (facts w)) (fun (s : pset) (u : ultrafilter s) => proj2 (proj2 (proj2 u))).

Open Scope bool_scope.
Infix    "→"    := implb    (at level 50) : bool_scope.
Notation "¬ x"  := (negb x) (at level 50) : bool_scope.

Section bool_lemmas.
    Definition demorgish : forall s t : bool, ~((s = true) /\ (t = true)) -> ((s = false) \/ (t = false))
        :=  fun s : bool => bool_ind
                (fun t : bool => ~((s = true) /\ (t = true)) -> ((s = false) \/ (t = false)))
                (fun n : ~((s = true) /\ (true = true)) => or_introl
                    (bool_ind (fun b : bool => ~((b = true) /\ (true = true)) -> (b = false))
                        (fun m : ~((true = true) /\ (true = true)) => False_ind (true = false) (m (conj eq_refl eq_refl)))
                        (fun _  => eq_refl) s n))
                (fun _ => or_intror eq_refl).

    Definition sflortfltosntfl : forall s t : bool, ((s = false) \/ (t = false)) -> ((s && t) = false)
        := fun s t : bool => or_ind (fun c : s = false => f_equal  (fun b : bool =>  b && t) c)
                                    (fun d : t = false => bool_ind (fun b : bool => (b && t) = false) d eq_refl s).

    Definition tnf : true <> false := eq_ind true (fun c : bool => if c then True else False) I false.

    Definition sorttrtostrorttr : forall s t : bool, (s || t) = true -> ((s = true) \/ (t = true))
        := fun s t : bool => bool_ind   (fun b : bool => (b || t) = true -> (b = true) \/ (t = true))
                                        (fun e : true = true => or_introl e)
                                        (fun e : t = true => or_intror e) s.

    Definition nttof : forall s : bool, s <> true -> s = false
        := bool_ind (fun s : bool => (s <> true) -> s = false)
                    (fun n : true <> true => False_ind (true = false) (n eq_refl))
                    (fun _ : false <> true => eq_refl).

    Definition bnttont : forall s : bool, s <> true -> ¬s = true
        := bool_ind (fun s : bool => (s <> true) -> (¬s = true))
                    (fun n : true <> true => False_ind (false = true) (n eq_refl))
                    (fun _ : false <> true => eq_refl).

    Definition nftot : forall s : bool, s <> false -> s = true
        := bool_ind (fun s : bool => s <> false -> s = true) (fun _ => eq_refl)
            (fun n : false <> false => False_ind (false = true) (n eq_refl)).

    Definition randbool : forall b c : bool, ¬b = c -> b = ¬c
        := fun b c : bool => bool_ind (fun s : bool => ¬s = c -> s = ¬c)
                                (fun e : false = c => f_equal negb e) (fun e : true = c => f_equal negb e) b.

    Definition dubneg : forall b : bool, b = ¬(¬b) := bool_ind (fun b : bool => b = ¬(¬b)) eq_refl eq_refl.

    Definition sflottr2sittr : forall s t : bool, (¬s = true) \/ (t = true) -> (s→t) = true
        :=  fun s t : bool =>
            or_ind  (fun c : ¬s = true => f_equal (fun b : bool => b→t) (eq_trans (dubneg s) (f_equal negb c)))
                    (fun d : t = true => bool_ind (fun b : bool => (b→t) = true) d eq_refl s).
End bool_lemmas.

Section prop_lemmas.
    Definition pandcomm : forall p q : prop, (p and q) entails (q and p)
        := fun p q : prop => p_and_i (p and q) q p (p_and_e2 p q) (p_and_e1 p q).

    Definition propdist1a : forall p q r : prop, (p and (q or r)) entails ((p and q) or (p and r))
        := fun p q r : prop =>
            entail_trans (p and (q or r)) ((q or r) and p) ((p and q) or (p and r))
            (pandcomm p (q or r))
            (residual_law2 (q or r) p ((p and q) or (p and r))
                (p_or_e q r (p implies ((p and q) or (p and r)))
                    (residual_law1 q p ((p and q) or (p and r))
                        (entail_trans (q and p) (p and q) ((p and q) or (p and r)) (pandcomm q p) (p_or_i1 (p and q) (p and r))))
                    (residual_law1 r p ((p and q) or (p and r))
                        (entail_trans (r and p) (p and r) ((p and q) or (p and r)) (pandcomm r p) (p_or_i2 (p and q) (p and r)))))).

    Definition propdemo : forall p q : prop, ((not p) and (not q)) entails (not (p or q))
        := fun p q : prop =>
            entail_trans ((not p) and (not q)) ((p or q) implies falsity) (not (p or q))
                (residual_law1 ((not p) and (not q)) (p or q) falsity
                    (entail_trans (((not p) and (not q)) and (p or q))
                        ((((not p) and (not q)) and p) or (((not p) and (not q)) and q))
                        falsity (propdist1a ((not p) and (not q)) p q)
                        (p_or_e (((not p) and (not q)) and p) (((not p) and (not q)) and q) falsity
                           (entail_trans (((not p) and (not q)) and p) (p and (not p)) falsity
                                (p_and_i (((not p) and (not q)) and p) p (not p)
                                    (p_and_e2 ((not p) and (not q)) p)
                                    (entail_trans (((not p) and (not q)) and p) ((not p) and (not q)) (not p)
                                        (p_and_e1 ((not p) and (not q)) p)
                                        (p_and_e1 (not p) (not q))))
                                (p_not_comp p))
                            (entail_trans (((not p) and (not q)) and q) (q and (not q)) falsity
                                (p_and_i (((not p) and (not q)) and q) q (not q)
                                    (p_and_e2 ((not p) and (not q)) q)
                                    (entail_trans (((not p) and (not q)) and q) ((not p) and (not q)) (not q)
                                        (p_and_e1 ((not p) and (not q)) q)
                                        (p_and_e2 (not p) (not q))))
                                (p_not_comp q)))))
                (pif_p_not_p (p or q)).

    Definition disjcs : forall (p q : prop) (w : world), (tv (p or q) w) = false -> ((tv p w) = false) /\ ((tv q w) = false)
        :=  fun (p q : prop) (w : world) (e : (tv (p or q) w) = false) =>
            conj    (nttof (tv p w) (fun c : (tv p w) = true => tnf (eq_trans (eq_sym (upcl w p (p or q) c (p_or_i1 p q))) e)))
                    (nttof (tv q w) (fun c : (tv q w) = true => tnf (eq_trans (eq_sym (upcl w q (p or q) c (p_or_i2 p q))) e))).

    (* This is definitely not the most efficient way of proving this- gotta work on it *)
    (* should be in prop_thms, but mvngout depends on it *)
    Definition p_not_ax      : forall (p : prop) (w : world), (tv (not p) w) = ¬(tv p w)
        :=  fun (p : prop) (w : world) => or_ind
                (fun e : (tv p w) = true =>
                   eq_ind true (fun b : bool => (tv (not p) w) = ¬b)
                      (nttof (tv (not p) w)
                         (fun d : (tv (not p) w) = true =>
                            tnf (eq_trans   (eq_sym (upcl w (p and (not p)) falsity (ancl w p (not p) e d) (p_not_comp p)))
                                            (consist w))))
                      (tv p w) (eq_sym e))
                (fun e : (tv (not p) w) = true =>
                   eq_ind true (fun b : bool => b = ¬(tv p w))
                      (eq_sym (bnttont (tv p w)
                            (fun d : (tv p w) = true =>
                                tnf (eq_trans   (eq_sym (upcl w (p and (not p)) falsity (ancl w p (not p) d e) (p_not_comp p)))
                                                (consist w)))))
                      (tv (not p) w) (eq_sym e))
                (stalis w p).

    Definition mvngout : forall (p : prop) (w : world) (b : bool), (tv p w) = b -> (tv (not p) w) = ¬b
        := fun (p : prop) (w : world) (b : bool) (e : (tv p w) = b) => eq_trans (p_not_ax p w) (f_equal negb e).

    Definition pimplies_true : forall (p q : prop) (w : world), (tv (p implies q) w) = true -> ((tv p w) → (tv q w)) = true
        :=  fun (p q : prop) (w : world) (e : (tv (p implies q) w) = true) =>
            sflottr2sittr (tv p w) (tv q w)
                (or_ind (fun x : (tv (not p) w) = true => or_introl (eq_trans (eq_sym (p_not_ax p w)) x))
                        (fun y : (tv q w) = true => or_intror y)
                        (bool_ind
                            (fun b : bool => (tv q w) = b -> ((tv (not p) w) = true) \/ ((tv q w) = true))
                            (fun c : (tv q w) = true => or_intror c)
                            (fun d : (tv q w) = false =>
                                or_introl (or_ind
                                    (fun m : (tv p w) = true =>
                                        False_ind ((tv (not p) w) = true)
                                            (tnf (eq_trans (eq_sym (upcl w ((p implies q) and p) q
                                                                            (ancl w (p implies q) p e m)
                                                                            (residual_law2 (p implies q) p q
                                                                            (entail_refl (p implies q))))) d)))
                                      (fun n : (tv (not p) w) = true => n)
                                      (stalis w p)))
                            (tv q w) eq_refl)).

    Definition pimplies_false : forall (p q : prop) (w : world), (tv (p implies q) w) = false -> ((tv p w) → (tv q w)) = false
        :=  fun (p q : prop) (w : world) (e : (tv (p implies q) w) = false) =>
            f_equal2 implb
                (nftot (tv p w)
                     (fun c : (tv p w) = false =>
                        tnf (eq_trans
                                (eq_sym (upcl w (not p) (p implies q) (mvngout p w false c)
                                    (residual_law1 (not p) p q
                                        (entail_trans ((not p) and p) (p and (not p)) q
                                            (pandcomm (not p) p)
                                            (entail_trans (p and (not p)) falsity q (p_not_comp p) (falsity_bot q))))))
                                e)))
                (nttof (tv q w)
                     (fun d : (tv q w) = true =>
                        tnf (eq_trans (eq_sym (upcl w q (p implies q) d (residual_law1 q p q (p_and_e1 q p)))) e))).
End prop_lemmas.

(* potential plan: split these up into cases- ie ∀p,q,w.[(p and q)@w = true -> (p@w = true) /\ (q@w = true)], etc. *)
Section prop_thms.
    Definition p_and_ax      : forall (p q : prop) (w : world), (tv (p  and    q) w) = ((tv p w) && (tv q w))
        := fun (p q : prop) (w : world) =>
            eq_sym (bool_ind (fun b : bool => ((tv (p and q) w) = b) -> (((tv p w) && (tv q w)) = b))
                            (fun e : (tv (p and q) w) = true => f_equal2 andb   (upcl w (p and q) p e (p_and_e1 p q))
                                                                                (upcl w (p and q) q e (p_and_e2 p q)))
                            (fun e : tv (p and q) w = false => sflortfltosntfl (tv p w) (tv q w) (demorgish (tv p w) (tv q w)
                                (and_ind (fun (a : (tv p w) = true) (b : (tv q w) = true) =>
                                    tnf (eq_trans (eq_sym (ancl w p q a b)) e)))))
                            (tv (p and q) w) eq_refl).

    Definition p_or_ax : forall (p q : prop) (w : world), (tv (p or q) w) = ((tv p w) || (tv q w))
        := fun (p q : prop) (w : world) =>
            eq_sym (bool_ind (fun b : bool => (tv (p or q) w) = b -> ((tv p w) || (tv q w)) = b)
                    (fun e : (tv (p or q) w) = true =>
                        bool_ind (fun b : bool => (tv p w) = b -> (b || (tv q w)) = true) (fun _ => eq_refl)
                            (fun c : (tv p w) = false =>
                                nftot (tv q w)
                                    (fun d : (tv q w) = false =>
                                        tnf (eq_trans (eq_sym e)
                                                (randbool (tv (p or q) w) true
                                                    (eq_trans (eq_sym (p_not_ax (p or q) w))
                                                        (upcl w ((not p) and (not q)) (not (p or q))
                                                            (ancl w (not p) (not q) (mvngout p w false c) (mvngout q w false d))
                                                            (propdemo p q)))))))
                            (tv p w)
                            eq_refl)
                    (fun e : (tv (p or q) w) = false => and_ind (fun a b => f_equal2 orb a b) (disjcs p q w e))
                    (tv (p or q) w)
                    eq_refl).

    Definition p_implies_ax  : forall (p q : prop) (w : world), (tv (p implies q) w) = ((tv p w) →  (tv q w))
        := fun (p q : prop) (w : world) => eq_sym (bool_ind (fun b : bool => (tv (p implies q) w) = b -> ((tv p w) → (tv q w)) = b)
        (pimplies_true p q w) (pimplies_false p q w) (tv (p implies q) w) eq_refl).

    Definition truth_ax      : forall w : world, (tv truth w) = true
        := fun w : world =>
            or_ind  (fun e : (tv truth w) = true => e)
                    (fun e : (tv (not truth) w) = true =>
                       False_ind ((tv truth w) = true)
                         (tnf   (eq_trans
                                    (eq_sym (upcl w (not truth) falsity e
                                         (entail_trans (not truth) (truth and (not truth)) falsity
                                            (p_and_i (not truth) truth (not truth)
                                                (truth_top (not truth)) (entail_refl (not truth)))
                                            (p_not_comp truth))))
                                    (consist w))))
                    (stalis w truth).

    Definition falsity_ax    : forall w : world, (tv falsity w) = false := consist.

    (* This too will surely need a revision or two *)
    Definition p_iff_ax      : forall (p q : prop) (w : world), (tv (p iff q) w) = ((tv (p implies q) w) && (tv (q implies p) w))
        :=  fun (p q : prop) (w : world) => eq_sym
            (   let piq := p implies q in
                let qip := q implies p in
                bool_ind    (fun b : bool => (tv (p iff q) w) = b -> (tv piq w) && (tv qip w) = b)
                            (fun e : (tv (p iff q) w) = true =>
                                f_equal2 andb   (upcl w (p iff q) piq e (p_iff_e1 p q))
                                                (upcl w (p iff q) qip e (p_iff_e2 p q)))
                            (fun e : (tv (p iff q) w) = false =>
                                sflortfltosntfl (tv piq w) (tv qip w)
                                    (demorgish (tv piq w) (tv qip w)
                                        (and_ind (fun (a : (tv piq w) = true) (b : (tv qip w) = true) =>
                                            tnf (eq_trans   (eq_sym (upcl w (piq and qip) (p iff q) (ancl w piq qip a b) (p_iff_i p q)))
                                                            e)))))
                            (tv (p iff q) w) eq_refl).

    Definition p_equals_ax   : forall (p q : prop) (w : world), ((tv (p equals q) w) = true) <-> (p = q)
        :=  fun (p q : prop) (w : world) =>
            conj    (fun e : (tv (p equals q) w) = true =>
                        proj1 (eq_two p q)
                            (conj   (truth_top (p equals q))
                                    (or_ind (fun c : (p equals q) ≡ truth   => proj2 c)
                                            (fun d : (p equals q) ≡ falsity =>
                                                False_ind (truth entails (p equals q))
                                                    (tnf (eq_trans  (eq_sym (upcl w (p equals q) falsity e (proj1 d)))
                                                                    (consist w))))
                                            (eq_one p q))))
                    (fun e : p = q => upcl w truth (p equals q) (truth_ax w) (proj2 (proj2 (eq_two p q) e))).

    (* haven't gotten to these just yet *)
    (* Definition p_exists_ax   : forall (R : prop -> prop) (w : world),
                                ((tv (p_exists R) w) = true) <-> (exists p : prop, (tv (R p) w) = true). *)
    (* Definition p_forall_ax   : forall (R : prop -> prop) (w : world),
                                ((tv (p_forall R) w) = true) <-> (forall p : prop, (tv (R p) w) = true). *)

    Definition complement : forall (p : prop) (w : world), (tv (p and (not p)) w) = false
        := fun (p : prop) (w : world) =>
            nttof   (tv (p and (not p)) w)
                    (fun e : (tv (p and (not p)) w) = true =>
                        tnf (eq_trans (eq_sym (upcl w (p and (not p)) falsity e (p_not_comp p))) (consist w))).

    Definition lem : forall (p : prop) (w : world), (tv (p or (not p)) w) = true
        :=  fun (p : prop) (w : world) =>
            or_ind  (fun e : (tv p w) = true => upcl w p (p or (not p)) e (p_or_i1 p (not p)))
                    (fun e : (tv (not p) w) = true => upcl w (not p) (p or (not p)) e (p_or_i2 p (not p)))
                    (stalis w p).

    (* might have to assume this one- can't say w/o proof irrelevance that all proofs that s is an ultrafilter are equal
        (and in fact may not be, without assuming proof irrelevance) *)
    (* Definition fact_inj : forall w v : world, (facts w) = (facts v) -> w = v. *)

    Definition all_ultras_worlds : forall s : pset, (ultrafilter s) -> exists w : world, s = (facts w)
        := fun (s : pset) (u : ultrafilter s) => ex_intro (fun w : world => s = facts w) (exist ultrafilter s u) eq_refl.

    (* (in)equality at one world means (in)equality in all worlds *)
    Definition eqiseqev : forall (p q : prop) (w : world),
        (tv (p equals q) w) = true -> forall u : world, (tv (p equals q) u) = true
        := fun (p q : prop) (w : world) (e : (tv (p equals q) w) = true) (u : world) =>
                proj2 (p_equals_ax p q u) (proj1 (p_equals_ax p q w) e).

    Definition neqisneqev : forall (p q : prop) (w : world),
                                (tv (p equals q) w) = false -> forall v : world, (tv (p equals q) v) <> true
        :=  fun (p q : prop) (w : world) (e : (tv (p equals q) w) = false) (v : world) (c : (tv (p equals q) v) = true) =>
            tnf (eq_trans (eq_sym (eqiseqev p q v c w)) e).
End prop_thms.

(* "enough ultrafilters" axiom: ⊢∀p,q:prop.[~(p entails q) -> ∃u:p -> bool.[(ultrafilter u) /\ ((u p) = true) /\ ((u q) = false]] *)
(* aka: ⊢∀p,q:prop.[~(p entails q) -> ∃w:world.[((tv p w) = true) /\ ((tv q w) = false]] *)
