(* CDS_primitives- all basics which don't involve extensions *)

Axiom e         : Set.
Axiom prop      : Set.  (* renaming so "p" can be used as a variable over prop's *)
Axiom truth     : prop.
Axiom falsity   : prop.
Axiom p_not     : prop -> prop.
Axiom p_and     : prop -> prop -> prop.
Axiom p_or      : prop -> prop -> prop.
Axiom p_implies : prop -> prop -> prop.
Axiom p_iff     : prop -> prop -> prop.
Axiom p_equals  : prop -> prop -> prop. (* TODO: p_equals/exists/forall should be parameterized over Stat's *)
Axiom p_exists  : (prop -> prop) -> prop.
Axiom p_forall  : (prop -> prop) -> prop.

(* Adding a new "sem_scope" for these notations- hopefully we'll be able to use "not" w/o conflicts *)
Infix "and"         := p_and        (at level 80)   : sem_scope.
Infix "or"          := p_or         (at level 80)   : sem_scope.
Infix "implies"     := p_implies    (at level 80)   : sem_scope.
Infix "iff"         := p_iff        (at level 80)   : sem_scope.
Infix "equals"      := p_equals     (at level 80)   : sem_scope.
Notation "'not' p"  := (p_not p)    (at level 80)   : sem_scope.

(* Stat, homo/heterogeneous Vectors *)
(* The type of Static semantic types consists of two parts:
    1. The Set-predicate static which consists of proofs certain Set's are static types
    2. The type Stat which will a subtype consisting of a Set s and a term of type (static s)-
        a proof that s is indeed a static sem type *)

(* Ok, so I wanted to prove that proofs of static s are unique, which turned out to be quite the challenge.
    Part of the way I made it easier (possible?) was to define "statterm" inductively, then define a function mapping
    each "statterm" to the appropriate type. Hopefully this won't cause any problems later on, but anyway it's only so
    I could prove proof uniqueness (which still sucked! I just hope it'll be useful!) *)

Inductive statterm : Set := ent : statterm | prp : statterm | func : statterm -> statterm -> statterm.
    (* Definition statterm_rect : forall P : statterm -> Type, (P ent) -> (P prp)
                                    -> (forall s : statterm, (P s) -> forall t : statterm, (P t) -> (P (func s t)))
                                        -> forall s : statterm, (P s) *)
    (* statterm_rect = fun (P : statterm -> Type) (x : P ent) (y : P prp)
            (f : forall s : statterm, P s -> forall t : statterm, P t -> P (func s t)) =>
            fix g (s : statterm) : P s :=
            match s as t return (P t) with
                | ent       => x
                | prp       => y
                | func a b  => f a (g a) b (g b)
            end *)

(* Mapping statterms to the appropriate sense type *)
Definition Sns  : statterm -> Set := statterm_rect (fun _ => Set) e prop (fun _ A _ B => A -> B).
    (*  Somewhat informally,
        Sns := λs:statterm. match s with
                                | ent       => e
                                | prp       => prop
                                | func a b  => (Sns a) -> (Sns b)
                            end *)

(* Mapping statterms to the appropriate extensional type *)
Definition Ext  : statterm -> Set := statterm_rect (fun _ => Set) e bool (fun s _ _ B => (Sns s) -> B).
    (*  Again informally,
        Ext := λs:statterm. match s with
                                | ent       => e
                                | prp       => bool
                                | func a b  => (Sns a) -> (Ext b)
                            end *)

(* Homogeneous vectors (over any type universe) and Heterogeneous vectors (map length-n vectors of statterms [s₀,…,sₙ₋₁]
    to length-n strings of terms of type (Sns sᵢ) ∀0≤i<n) *)
(* TODO: make some args implicit? Operations on (Het)Vect? Notations? ([],::,[x,y,z],…) *)

Inductive Vect (A : Type) : nat -> Type :=
    | vnil  : Vect A 0
    | vcons : forall n : nat, A -> Vect A n -> Vect A (S n).
Inductive HetVect : forall n : nat, Vect statterm n -> Set :=
    | hnil  : HetVect 0 (vnil statterm)
    | hcons : forall (n : nat) (t : Vect statterm n) (s : statterm),
                (Sns s) -> (HetVect n t) -> (HetVect (S n) (vcons statterm n s t)).

(* map [s₀,s₁,…,sₙ] to s₀*(s₁*(…*sₙ)) *)
Fixpoint type_str (n : nat) (v : Vect statterm n) {struct v} : Set :=
    match v with
        | vnil          => unit
        | vcons 0 s _   => Sns s
        (* | vcons k s r   => prod (Sns s) (type_str k r) *)
        | vcons k s r   => ((Sns s)*(type_str k r))%type
    end.

(* If we wanna add some vector notations *)
(* Module VectNotes.
    Notation "[]" := (vnil _) (at level 0) : vect_scope.
    Infix "::" := (vcons _ _) (at level 60, right associativity) : vect_scope.
    Open Scope vect_scope.
    Notation "[ x ]" := ((x :: [])) (at level 0) : vect_scope.
    Notation "[ x , .. , y ]" := ((vcons _ _ x .. (vcons _ _ y (vnil _)) ..)) (at level 0) : vect_scope.
    End VectNotes.
    Import VectNotes. *)
