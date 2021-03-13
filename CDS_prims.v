(* CDS_prims- (hopefully) the final version *)
Axiom e prop world                  : Set.
Axiom w0                            : world.
Axiom tv                            : prop -> world -> bool.
Axiom truth falsity                 : prop.
Axiom p_not                         : prop -> prop.
Axiom p_and p_or p_implies p_iff    : prop -> prop -> prop.

Section Statterm.
    Inductive statterm : Set := ent : statterm | prp : statterm | func : statterm -> statterm -> statterm.

    (* Mapping statterms to the appropriate sense type *)
    Fixpoint Sns (s : statterm) : Set
        :=  match s with
                | ent       => e
                | prp       => prop
                | func a b  => (Sns a) -> (Sns b)
            end.

    (* Mapping statterms to the appropriate extensional type *)
    Fixpoint Ext (s : statterm) : Set
        :=  match s with
                | ent       => e
                | prp       => bool
                | func a b  => (Sns a) -> (Ext b)
            end.

    (* Definition of the "@" function *)
    Fixpoint ext_at (s : statterm) : (Sns s) -> world -> (Ext s)
        :=  match s as t return ((Sns t) -> world -> (Ext t)) with
                | ent       => fun (x : e) (w : world) => x
                | prp       => tv
                | func a b  => fun (f : (Sns a) -> (Sns b)) (w : world) (x : Sns a) => ext_at b (f x) w
            end.
End Statterm.

Axiom p_equals                      : forall s : statterm, (Sns s) -> (Sns s) -> prop.
Axiom p_exists p_forall             : forall s : statterm, ((Sns s) -> prop) -> prop.

Module Sem_notations.
    (* Adding a new "sem_scope" for these notations- should allow us to use "not" w/o naming conflicts *)
    Infix "and"         := p_and            (at level 80)   : sem_scope.
    Infix "or"          := p_or             (at level 80)   : sem_scope.
    Infix "implies"     := p_implies        (at level 80)   : sem_scope.
    Infix "iff"         := p_iff            (at level 80)   : sem_scope.
    Infix "equals"      := (p_equals prp)   (at level 80)   : sem_scope.
    Notation "'not' p"  := (p_not p)        (at level 80)   : sem_scope.
    Notation "p @ w"    := (tv p w)         (at level 80)   : sem_scope. (* hopefully this'll make the theorems way more legible! *)
    Open Scope sem_scope.
    (* we'll see if I make another bool_prims file, in which case these 3 lines'll go in there *)
    Infix    "~>"       := implb            (at level 50)   : bool_scope.
    Notation "-~ x"     := (negb x)         (at level 50)   : bool_scope.
    Open Scope bool_scope.
End Sem_notations.
Import Sem_notations.

(*  Ok, so this last part uses Coq's module system to define the ultrafilter here but defining entails in extensions.v
    Feel free to ignore the details of how this works (this stuff's annoyed me since the days I was messing around with OCaml),
    but here's a brief explanation:
    Basically, I'm defining a type of "file" (aka a module) and what such a file must contain to be well-typed (this is Ent).
    In this case, all I require of modules of the type Ent is that they provide a term p_entails of type prop -> prop -> Prop.
    Then, I define Ult which is a "functor" (their word) on files/modules of this type, meaning that it takes modules which are
    of type Ent and returns another module (modules aren't required to have types, since they're language-external notions).
    From there, I can make all of my definitions in terms of the p_entails provided by the argument module. *)
Module Type Ent.
    Parameter p_entails : prop -> prop -> Prop.
End Ent.

Module Ult (E : Ent).
    Definition p_equiv : prop -> prop -> Prop := fun p q : prop => (E.p_entails p q) /\ (E.p_entails q p).
    Infix "entails"     := E.p_entails  (at level 80)   : sem_scope.
    Infix "≡"           := p_equiv      (at level 80)   : sem_scope.

    Definition pset : Set := prop -> bool.
    Definition facts: world -> pset := fun (w : world) (p : prop) => tv p w.

    Definition uc  : pset -> Prop := fun s : pset => forall p q : prop,  (s p) = true  -> p entails q -> (s q) = true.
    Definition ac  : pset -> Prop := fun s : pset => forall p q : prop,  (s p) = true  -> (s q) = true -> (s (p and q)) = true.
    Definition sai : pset -> Prop := fun s : pset => forall p   : prop, ((s p) = true) \/ ((s (not p)) = true).
    Definition cst : pset -> Prop := fun s : pset => (s falsity) = false.
    Definition ultrafilter : pset -> Prop := fun s : pset => (uc s) /\ (ac s) /\ (sai s) /\ (cst s).

    Axiom facts_inj  : forall w v : world, (facts w) = (facts v) -> w = v.
    Axiom facts_onto : forall s : pset, (ultrafilter s) -> exists w : world, s = (facts w).
End Ult.


