(* A new plan for identifying PTypes and phenom_terms--- mutually inductive predicates rather than Set types *)

(* Just a few basic definitions I like to have when I define things--- B,C,I combinators, feq's, eq_ind_dep, eq_trans' *)
Module Import   Some_Basics.
    (* B, C, and I combinators (respectively) for representing linear functions via combinators *)
    Definition comp : forall {A B C : Type}, (B -> C) -> (A -> B) -> A -> C := fun (A B C : Type) (f : B -> C) (g : A -> B) (x : A) => f (g x).
    (* Infix "∘" := comp (at level 20). *)
    Definition flip : forall {A B C : Type}, (A -> B -> C) -> B -> A -> C := fun (A B C : Type) (f : A -> B -> C) (y : B) (x : A) => f x y.
    Definition id : forall {A : Type}, A -> A := fun (A : Type) (x : A) => x.

    (*  eq_ind_dep is a more general elimination schema for equality than the default, which allows for elim predicates that depend on the proof of equality itself;
        this is useful for proving certain meta-theorems about equality (for example, proving that (eq_sym (eq_sym e)) = e) *)
    Definition eq_ind_dep : forall {A : Type} (x : A) (P : forall z : A, x = z -> Prop), P x eq_refl -> forall (y : A) (e : x = y), P y e
        :=  fun (A : Type) (x : A) (P : forall z : A, x = z -> Prop) (p : P x eq_refl) (y : A) (e : x = y) =>
            match e as d in (_ = z) return (P z d) with eq_refl => p end.
    (* eq_trans' is simply a proof of the transitivity of equality, but framed as "any two things that are both equal to the some third thing are themselves equal" *)
    Definition eq_trans' : forall {A : Type} {x y z : A}, x = y -> x = z -> y = z
        :=  fun (A : Type) (x y z : A) (u : x = y) (v : x = z) => eq_ind x (flip eq z) v y u.
    (* proofs of the example above for where/when eq_ind_dep is useful *)
    Definition eq_sym_inv : forall {A : Type} {x y : A} (e : x = y), e = (eq_sym (eq_sym e))
        := fun (A : Type) (x : A) => eq_ind_dep x (fun (y : A) (e : x = y) => e = (eq_sym (eq_sym e))) eq_refl.
    Definition eq_sym_inv_sym : forall {A : Type} {x y : A} (e : x = y), (eq_sym (eq_sym e)) = e
        := fun (A : Type) (x : A) => eq_ind_dep x (fun (y : A) (e : x = y) => (eq_sym (eq_sym e)) = e) eq_refl.


    (* feq, feq2, and feq3 are proofs that when applying a 1-3 place function to arguments known to be equal, the results are equal as well *)
    Definition feq  : forall {A B : Type} (f : A -> B) {x y : A}, x = y -> (f x) = (f y)
        :=  fun (A B : Type) (f : A -> B) (x : A) => eq_ind x (fun z : A => (f x) = (f z)) eq_refl.
    Definition feq2 : forall {A B C : Type} (f : A -> B -> C) {x a : A} {y b : B}, x = a -> y = b -> (f x y) = (f a b)
        :=  fun (A B C : Type) (f : A -> B -> C) (x a : A) (y b : B) =>
            eq_ind x (fun z : A => y = b -> (f x y) = (f z b)) (feq (f x)) a.
    Definition feq3 : forall {A B C D : Type} (f : A -> B -> C -> D) {x a : A} {y b : B} {z c : C}, x = a -> y = b -> z = c -> (f x y z) = (f a b c)
        :=  fun (A B C D : Type) (f : A -> B -> C -> D) (x a : A) (y b : B) (z c : C) =>
            eq_ind x (fun d : A => y = b -> z = c -> (f x y z) = (f d b c)) (feq2 (f x)) a.
End             Some_Basics.

(* Assuming the string monoid for the phenogrammar *)
Module Import   String_Mon.
    Axiom string : Set.
    Axiom e : string.
    Axiom dot : string -> string -> string.
    Infix "·" := dot (at level 20) : str_scope.
    Open Scope str_scope.
    Axiom dot_Lid   : forall s : string, e·s = s.
    Axiom dot_Rid   : forall s : string, s·e = s.
    Axiom dot_assoc : forall s t u : string,(s·t)·u = s·(t·u).
End             String_Mon.

(* Generalized definitions of what are intended to be the definitions of A_ϕ, ɩ_ϕ, and say_ϕ, as well as proofs that ɩ_ϕ and say_ϕ are inverses for any ϕ (up to extensionality) *)
(* For their use in the context of PType's and phenominators, A will always be string, and f will be the B-phenominator *)
Section         Fine_Grain.
    Definition fine_grained : forall {A B : Set}, (A -> B) -> Set := fun (A B : Set) (f : A -> B) => {u : B & {v : A | u = (f v)}}.
    Definition iota : forall {A B : Set} (f : A -> B), A -> fine_grained f
        := fun (A B : Set) (f : A -> B) (x : A) => existT (fun u : B => {v : A | u = (f v)}) (f x) (exist (fun v : A => (f x) = (f v)) x eq_refl).
    Definition say  : forall {A B : Set} (f : A -> B), fine_grained f -> A
        := fun (A B : Set) (f : A -> B) (u : fine_grained f) => proj1_sig (projT2 u).
    (* Proving that, for a fixed f, (iota f) and (say f) are inverse functions (up to functional extensionality) *)
    Definition iota_say_inv : forall {A B : Set} (f : A -> B) (p : fine_grained f), (iota f (say f p)) = p
        :=  fun (A B : Set) (f : A -> B) (p : fine_grained f) =>
            match p as s return ((iota f (say f s)) = s) with
                | existT _ u (exist _ v e) =>
                    let Q := fun (y : B) (x : A) => y = (f x) in
                    let P := fun y : B => {x : A | Q y x} in
                    eq_trans    (eq_ind_dep (f v) (fun (z : B) (d : (f v) = z) => (existT P (f v) (exist (Q (f v)) v eq_refl)) = (existT P z (exist (Q z) v (eq_sym d)))) eq_refl u (eq_sym e))
                                (feq (fun d : u = (f v) => existT P u (exist (Q u) v d)) (eq_sym_inv_sym e))
            end.
    (* Actually, this second one can be proved without the assumption of the x : A argument *)
    Definition say_iota_inv : forall {A B : Set} (f : A -> B) (x : A), (say f (iota f x)) = x := fun (A B : Set) (f : A -> B) (x : A) => eq_refl.
End             Fine_Grain.


Inductive   PType       : Set -> Prop
    :=  st      : PType string
    |   func    : forall A B : Set, PType A -> PType B -> PType (A -> B)
    (* can I remove the PType requirement from here too (as below)? Since phenom_term (string -> A) _ being inhabited ought to imply (PType A)? *)
    |   fine    : forall (A : Set) (f : string -> A), phenom_term (string -> A) f -> PType (fine_grained f)
with        phenom_term : forall A : Set, A -> Prop
    :=  pemp    : phenom_term string e
    |   pdot    : phenom_term (string -> string -> string) dot
    |   pid     : forall A : Set, PType A -> phenom_term (A -> A) id
    |   pcomp   : forall A B C : Set, PType A -> PType B -> PType C -> phenom_term ((B -> C) -> (A -> B) -> A -> C) comp
    |   pflip   : forall A B C : Set, PType A -> PType B -> PType C -> phenom_term ((A -> B -> C) -> B -> A -> C) flip
    (*  I need the proof that B is a PType here b/c otherwise I'm having trouble proving that any set A, if ∃f:A.[phenom_term A f], then A is a PType otherwise-
        I still feel like it should be provable without the (PType B) argument though *)
    |   papp    : forall A B : Set, PType B -> forall (f : A -> B) (x : A), phenom_term (A -> B) f -> phenom_term A x -> phenom_term B (f x)
    |   piota   : forall (A : Set) (f : string -> A), phenom_term (string -> A) f -> phenom_term (string -> fine_grained f) (iota f)
    |   psay    : forall (A : Set) (f : string -> A), phenom_term (string -> A) f -> phenom_term (fine_grained f -> string) (say f).

(* definition of syntactic categories, including mapping functions from Lambek & HTLCG categories into LCG tectos *)
Module Import   Syntax.
    Axiom Atom : Set. (* Assuming a type for atomic syntactic categories *)

    Inductive Lambek : Set := At : Atom -> Lambek | FS : Lambek -> Lambek -> Lambek | BS : Lambek -> Lambek -> Lambek.
    Infix "/" := FS : syn_scope.
    Infix "\" := BS (at level 30, right associativity) : syn_scope.

    Inductive HybCat : Set := Lam : Lambek -> HybCat | VS : HybCat -> HybCat -> HybCat.
    Infix "↾" := VS (at level 40, left associativity) : syn_scope.

    Inductive Tecto : Set := TAt : Atom -> Tecto | LI : Tecto -> Tecto -> Tecto.
    Infix "⊸" := LI (at level 30, right associativity) : syn_scope.

    Open Scope syn_scope.

    Definition LamTec : Lambek -> Tecto
        := Lambek_rec (fun _ : Lambek => Tecto) TAt (fun (_ : Lambek) (Y : Tecto) (_ : Lambek) (X : Tecto) => X ⊸ Y) (fun (_ : Lambek) (X : Tecto) (_ : Lambek) (Y : Tecto) => X ⊸ Y).
    Definition HybTec : HybCat -> Tecto
        := HybCat_rec (fun _ : HybCat => Tecto) LamTec (fun (_ : HybCat) (Y : Tecto) (_ : HybCat) (X : Tecto) => X⊸Y).
End             Syntax.


(* lemma: every Set which has a phenom_term is itself a PType *)
(* now provable thanks to addition of (PType B) arg in papp constructor *)
Definition phenPTyp : forall (A : Set) (x : A), phenom_term A x -> PType A
    :=  phenom_term_ind (fun (A : Set) (_ : A) => PType A)
            st
            (func string (string -> string) st (func string string st st))
            (fun (A : Set) (p : PType A) => func A A p p)
            (fun (A B C : Set) (p : PType A) (q : PType B) (r : PType C) => func (B -> C) ((A -> B) -> A -> C) (func B C q r) (func (A -> B) (A -> C) (func A B p q) (func A C p r)))
            (fun (A B C : Set) (p : PType A) (q : PType B) (r : PType C) => func (A -> B -> C) (B -> A -> C) (func A (B -> C) p (func B C q r)) (func B (A -> C) q (func A C p r)))
            (fun (A B : Set) (p : PType B) (f : A -> B) (x : A) (_ : phenom_term (A -> B) f) (_ : PType (A -> B)) (_ : phenom_term A x) (_ : PType A) => p)
            (fun (A : Set) (f : string -> A) (p : phenom_term (string -> A) f) (_ : PType (string -> A)) => func string (fine_grained f) st (fine A f p))
            (fun (A : Set) (f : string -> A) (p : phenom_term (string -> A) f) (_ : PType (string -> A)) => func (fine_grained f) string (fine A f p) st).


(* Todo: introduce slash notation for phenominator/PType shorthands *)
Fixpoint convert (l : Lambek) {struct l} : {A : Set & {f : string -> A | phenom_term (string -> A) f}}
    :=  match l with
            | At _  => existT (fun A : Set => {f : string -> A | phenom_term (string -> A) f}) string (exist (fun f : string -> string => phenom_term (string -> string) f) id (pid string st))
            | Y / X =>
                match convert X,convert Y with existT _ A (exist _ f p),existT _ B (exist _ g q) =>
                    existT  (fun Z : Set => {h : string -> Z | phenom_term (string -> Z) h}) (fine_grained f -> fine_grained g)
                            (exist  (phenom_term (string -> fine_grained f -> fine_grained g))
                                    (fun (v : string) (u : fine_grained f) => iota g (v·(say f u)))
                                    (papp   (string -> fine_grained f -> string) (string -> fine_grained f -> fine_grained g)
                                            (func string (fine_grained f -> fine_grained g) st (func (fine_grained f) (fine_grained g) (fine A f p) (fine B g q)))
                                            (comp (comp (iota g))) (flip (comp comp dot) (say f))
                                            (papp   ((fine_grained f -> string) -> fine_grained f -> fine_grained g) ((string -> fine_grained f -> string) -> string -> fine_grained f -> fine_grained g)
                                                    (func   (string -> fine_grained f -> string) (string -> fine_grained f -> fine_grained g)
                                                            (func string (fine_grained f -> string) st (func (fine_grained f) string (fine A f p) st))
                                                            (func string (fine_grained f -> fine_grained g) st (func (fine_grained f) (fine_grained g) (fine A f p) (fine B g q))))
                                                    comp (comp (iota g))
                                                    (pcomp  string (fine_grained f -> string) (fine_grained f -> fine_grained g)
                                                            st (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) (fine_grained g) (fine A f p) (fine B g q)))
                                                    (papp   (string -> fine_grained g) ((fine_grained f -> string) -> fine_grained f -> fine_grained g)
                                                            (func   (fine_grained f -> string) (fine_grained f -> fine_grained g)
                                                                    (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) (fine_grained g) (fine A f p) (fine B g q)))
                                                            comp (iota g)
                                                            (pcomp (fine_grained f) string (fine_grained g) (fine A f p) st (fine B g q))
                                                            (piota B g q)))
                                            (papp   (fine_grained f -> string) (string -> fine_grained f -> string)
                                                    (func string (fine_grained f -> string) st (func (fine_grained f) string (fine A f p) st))
                                                    (flip (comp comp dot)) (say f)
                                                    (papp   (string -> (fine_grained f -> string) -> fine_grained f -> string) ((fine_grained f -> string) -> string -> fine_grained f -> string)
                                                            (func   (fine_grained f -> string) (string -> fine_grained f -> string)
                                                                    (func (fine_grained f) string (fine A f p) st) (func string (fine_grained f -> string) st (func (fine_grained f) string (fine A f p) st)))
                                                            flip (comp comp dot)
                                                            (pflip  string (fine_grained f -> string) (fine_grained f -> string)
                                                                    st (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) string (fine A f p) st))
                                                            (papp   (string -> string -> string) (string -> (fine_grained f -> string) -> fine_grained f -> string)
                                                                    (func   string ((fine_grained f -> string) -> fine_grained f -> string)
                                                                            st (func    (fine_grained f -> string) (fine_grained f -> string)
                                                                                        (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) string (fine A f p) st)))
                                                                    (comp comp) dot
                                                                    (papp   ((string -> string) -> (fine_grained f -> string) -> fine_grained f -> string)
                                                                            ((string -> string -> string) -> string -> (fine_grained f -> string) -> fine_grained f -> string)
                                                                            (func   (string -> string -> string) (string -> (fine_grained f -> string) -> fine_grained f -> string)
                                                                                    (func   string (string -> string) st (func string string st st))
                                                                                    (func   string ((fine_grained f -> string) -> fine_grained f -> string)
                                                                                            st  (func   (fine_grained f -> string) (fine_grained f -> string)
                                                                                                        (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) string (fine A f p) st))))
                                                                            comp comp
                                                                            (pcomp  string (string -> string) ((fine_grained f -> string) -> fine_grained f -> string)
                                                                                    st (func string string st st)
                                                                                    (func   (fine_grained f -> string) (fine_grained f -> string)
                                                                                            (func (fine_grained f) string (fine A f p) st)
                                                                                            (func (fine_grained f) string (fine A f p) st)))
                                                                            (pcomp (fine_grained f) string string (fine A f p) st st))
                                                                    pdot))
                                                            (psay A f p))))
                end
            | X \ Y =>
                match convert X,convert Y with existT _ A (exist _ f p),existT _ B (exist _ g q) =>
                    existT  (fun Z : Set => {h : string -> Z | phenom_term (string -> Z) h})
                            (fine_grained f -> fine_grained g)
                            (exist  (phenom_term (string -> fine_grained f -> fine_grained g))
                                    (fun (v : string) (u : fine_grained f) => iota g ((say f u)·v))
                                    (papp   (string -> fine_grained f -> string) (string -> fine_grained f -> fine_grained g)
                                            (func string (fine_grained f -> fine_grained g) st (func (fine_grained f) (fine_grained g) (fine A f p) (fine B g q)))
                                            (comp (comp (iota g))) (flip (comp dot (say f)))
                                            (papp   ((fine_grained f -> string) -> fine_grained f -> fine_grained g) ((string -> fine_grained f -> string) -> string -> fine_grained f -> fine_grained g)
                                                    (func   (string -> fine_grained f -> string) (string -> fine_grained f -> fine_grained g)
                                                            (func string (fine_grained f -> string) st (func (fine_grained f) string (fine A f p) st))
                                                            (func string (fine_grained f -> fine_grained g) st (func (fine_grained f) (fine_grained g) (fine A f p) (fine B g q))))
                                                    comp (comp (iota g))
                                                    (pcomp  string (fine_grained f -> string) (fine_grained f -> fine_grained g)
                                                            st (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) (fine_grained g) (fine A f p) (fine B g q)))
                                                    (papp   (string -> fine_grained g) ((fine_grained f -> string) -> fine_grained f -> fine_grained g)
                                                            (func   (fine_grained f -> string) (fine_grained f -> fine_grained g)
                                                                    (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) (fine_grained g) (fine A f p) (fine B g q)))
                                                            comp (iota g)
                                                            (pcomp (fine_grained f) string (fine_grained g) (fine A f p) st (fine B g q))
                                                            (piota B g q)))
                                            (papp   (fine_grained f -> string -> string) (string -> fine_grained f -> string)
                                                    (func string (fine_grained f -> string) st (func (fine_grained f) string (fine A f p) st))
                                                    flip (comp dot (say f))
                                                    (pflip (fine_grained f) string string (fine A f p) st st)
                                                    (papp   (fine_grained f -> string) (fine_grained f -> string -> string)
                                                            (func (fine_grained f) (string -> string) (fine A f p) (func string string st st))
                                                            (comp dot) (say f)
                                                            (papp   (string -> string -> string) ((fine_grained f -> string) -> fine_grained f -> string -> string)
                                                                    (func   (fine_grained f -> string) (fine_grained f -> string -> string)
                                                                            (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) (string -> string) (fine A f p) (func string string st st)))
                                                                    comp dot
                                                                    (pcomp (fine_grained f) string (string -> string) (fine A f p) st (func string string st st))
                                                                    pdot)
                                                            (psay A f p)))))
                end
        end.
    (* older version, when papp didn't require (PType B) arg *)
    (* :=  match l with
            | At _  => existT (fun A : Set => {f : string -> A | phenom_term (string -> A) f}) string (exist (phenom_term (string -> string)) id (pid string st))
            | Y / X =>
                match convert X,convert Y with
                    existT _ A (exist _ f p),existT _ B (exist _ g q) =>
                    existT  (fun Z : Set => {h : string -> Z | phenom_term (string -> Z) h})
                            (fine_grained f -> fine_grained g)
                            (exist  (phenom_term (string -> fine_grained f -> fine_grained g))
                                    (fun (v : string) (u : fine_grained f) => iota g (v·(say f u)))
                                    (papp   (string -> fine_grained f -> string) (string -> fine_grained f -> fine_grained g) (comp (comp (iota g))) (flip (comp comp dot) (say f))
                                            (papp   ((fine_grained f -> string) -> fine_grained f -> fine_grained g) ((string -> fine_grained f -> string) -> string -> fine_grained f -> fine_grained g)
                                                    comp (comp (iota g))
                                                    (pcomp  string (fine_grained f -> string) (fine_grained f -> fine_grained g)
                                                            st (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) (fine_grained g) (fine A f p) (fine B g q)))
                                                    (papp   (string -> fine_grained g) ((fine_grained f -> string) -> fine_grained f -> fine_grained g) comp (iota g)
                                                            (pcomp (fine_grained f) string (fine_grained g) (fine A f p) st (fine B g q)) (piota B g q)))
                                            (papp   (fine_grained f -> string) (string -> fine_grained f -> string) (flip (comp comp dot)) (say f)
                                                    (papp   (string -> (fine_grained f -> string) -> fine_grained f -> string) ((fine_grained f -> string) -> string -> fine_grained f -> string)
                                                            flip (comp comp dot)
                                                            (pflip  string (fine_grained f -> string) (fine_grained f -> string)
                                                                    st (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) string (fine A f p) st))
                                                            (papp (string -> string -> string) (string -> (fine_grained f -> string) -> fine_grained f -> string) (comp comp) dot
                                                                    (papp   ((string -> string) -> (fine_grained f -> string) -> fine_grained f -> string)
                                                                            ((string -> string -> string) -> string -> (fine_grained f -> string) -> fine_grained f -> string)
                                                                            comp comp
                                                                            (pcomp  string (string -> string) ((fine_grained f -> string) -> fine_grained f -> string)
                                                                                    st (func string string st st)
                                                                                    (func   (fine_grained f -> string) (fine_grained f -> string)
                                                                                            (func (fine_grained f) string (fine A f p) st)
                                                                                            (func (fine_grained f) string (fine A f p) st)))
                                                                            (pcomp (fine_grained f) string string (fine A f p) st st))
                                                                    pdot))
                                                    (psay A f p))))
                end
            | X \ Y =>
                match convert X,convert Y with
                    existT _ A (exist _ f p),existT _ B (exist _ g q) =>
                    existT  (fun Z : Set => {h : string -> Z | phenom_term (string -> Z) h})
                            (fine_grained f -> fine_grained g)
                            (exist  (phenom_term (string -> fine_grained f -> fine_grained g))
                                    (fun (v : string) (u : fine_grained f) => iota g ((say f u)·v))
                                    (papp   (string -> fine_grained f -> string) (string -> fine_grained f -> fine_grained g) (comp (comp (iota g))) (flip (comp dot (say f)))
                                            (papp   ((fine_grained f -> string) -> fine_grained f -> fine_grained g) ((string -> fine_grained f -> string) -> string -> fine_grained f -> fine_grained g)
                                                    comp (comp (iota g))
                                                   (pcomp   string (fine_grained f -> string) (fine_grained f -> fine_grained g)
                                                            st (func (fine_grained f) string (fine A f p) st) (func (fine_grained f) (fine_grained g) (fine A f p) (fine B g q)))
                                                   (papp    (string -> fine_grained g) ((fine_grained f -> string) -> fine_grained f -> fine_grained g) comp (iota g)
                                                            (pcomp (fine_grained f) string (fine_grained g) (fine A f p) st (fine B g q))
                                                            (piota B g q)))
                                            (papp   (fine_grained f -> string -> string) (string -> fine_grained f -> string) flip (comp dot (say f))
                                                    (pflip (fine_grained f) string string (fine A f p) st st)
                                                    (papp   (fine_grained f -> string) (fine_grained f -> string -> string) (comp dot) (say f)
                                                            (papp (string -> string -> string) ((fine_grained f -> string) -> fine_grained f -> string -> string) comp dot
                                                                 (pcomp (fine_grained f) string (string -> string) (fine A f p) st (func string string st st)) pdot)
                                                            (psay A f p)))))
                end
        end. *)

(*  Making these returns Set's rather than {A : Set | PType A} b/c it'll be easier to work with in defining pros2phen & phen2pros;
    I'll make the proof that the outputs are always PType's into distinct theorems *)
Fixpoint pros (Z : HybCat) : Set
    :=  match Z with
            | Lam _ =>  string
            | Y ↾ X =>  pros X -> pros Y
        end.

Fixpoint phen (Z : HybCat) : Set
    :=  match Z with
          | Lam L =>    match (convert L) with existT _ A (exist _ f p) => fine_grained f end
          | Y ↾ X =>    phen X -> phen Y
          end.

(* Proofs that the output of pros and phen (respectively) are always PType's *)
Definition prosPType : forall Z : HybCat, PType (pros Z)
    := HybCat_ind (fun Z : HybCat => PType (pros Z)) (fun _ : Lambek => st) (fun (Y : HybCat) (q : PType (pros Y)) (X : HybCat) (p : PType (pros X)) => func (pros X) (pros Y) p q).
Definition phenPType : forall Z : HybCat, PType (phen Z)
    :=  HybCat_ind  (fun Z : HybCat => PType (phen Z))
                    (fun L : Lambek => match (convert L) as s return (PType (let (A,t) := s in let (f,_) := t in fine_grained f)) with existT _ A (exist _ f p) => fine A f p end)
                    (fun (Y : HybCat) (q : PType (phen Y)) (X : HybCat) (p : PType (phen X)) => func (phen X) (phen Y) p q).


Fixpoint pros2phen (Z : HybCat) : (pros Z) -> (phen Z)
    :=  match Z as h return (pros h -> phen h) with
            | Lam L => match (convert L) as s return (string -> (let (A,t) := s in let (f,_) := t in fine_grained f)) with existT _ A (exist _ f p) => iota f end
            | Y ↾ X => fun (f : pros X -> pros Y) (u : phen X) => pros2phen Y (f (phen2pros X u))
        end
with     phen2pros (Z : HybCat) : (phen Z) -> (pros Z)
    :=  match Z as h return (phen h -> pros h) with
            | Lam L => match (convert L) as s return ((let (A,t) := s in let (f,_) := t in fine_grained f) -> string) with existT _ A (exist _ f p) => say f end
            | Y ↾ X => fun (g : phen X -> phen Y) (v : pros X) => phen2pros Y (g (pros2phen X v))
        end.

(* Proof that pros2phen and phen2pros are inverses for any Z : HybCat requires functional extensionality in the vertical slash case *)
(* First requires functional extensionality, posited here *)
Axiom func_ext : forall {A B : Type} (f g : A -> B), (forall x : A, (f x) = (g x)) -> f = g.

(* Getting an actual definition that I can load w/o problems is proving to be tricky, so I'll just write this one in terms of the proof tactics *)
Theorem pros_phen_inv : forall Z : HybCat, ((comp (pros2phen Z) (phen2pros Z)) = id) /\ ((comp (phen2pros Z) (pros2phen Z)) = id).
Proof.
    (* gives most of the actual function definition, except for the base case (ie Lambek) *)
    refine  (HybCat_ind  (fun Z : HybCat => ((comp (pros2phen Z) (phen2pros Z)) = id) /\ ((comp (phen2pros Z) (pros2phen Z)) = id))
                    _
                    (fun (Y : HybCat) (H : ((comp (pros2phen Y) (phen2pros Y)) = id) /\ ((comp (phen2pros Y) (pros2phen Y)) = id))
                         (X : HybCat) (K : ((comp (pros2phen X) (phen2pros X)) = id) /\ ((comp (phen2pros X) (pros2phen X)) = id)) =>
                        match H,K with conj qrh qhr,conj prh phr =>
                            conj    (func_ext (comp (pros2phen (Y↾X)) (phen2pros (Y↾X))) id
                                        (fun g : phen X -> phen Y =>
                                            func_ext    (fun u : phen X => pros2phen Y (phen2pros Y (g (pros2phen X (phen2pros X u))))) g
                                                        (fun u : phen X =>
                                                            eq_ind u (fun p : phen X => (pros2phen Y (phen2pros Y (g p))) = (g u)) (feq (fun h : phen Y -> phen Y => h (g u)) qrh)
                                                                     (pros2phen X (phen2pros X u)) (eq_sym (feq (fun h : phen X -> phen X => h u) prh)))))
                                    (func_ext (comp (phen2pros (Y↾X)) (pros2phen (Y↾X))) id
                                        (fun f : pros X -> pros Y =>
                                            func_ext    (fun v : pros X => phen2pros Y (pros2phen Y (f (phen2pros X (pros2phen X v))))) f
                                                        (fun v : pros X =>
                                                            eq_ind v (fun p : pros X => (phen2pros Y (pros2phen Y (f p))) = (f v)) (feq (fun h : pros Y -> pros Y => h (f v)) qhr)
                                                                     (phen2pros X (pros2phen X v)) (eq_sym (feq (fun h : pros X -> pros X => h v) phr)))))
                        end)).
    (intro L; simpl).
    (destruct (convert L) as [A [f p]]).
    split.
     all: (apply func_ext).
     (apply iota_say_inv).
     (apply say_iota_inv).
Qed.
