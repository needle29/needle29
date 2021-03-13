(* Vect- file about the vectors we'll be using in the semantics *)

(* Load CDS_prims. *)

(* So I think this only schematizes over the predicative sorts: (Vect (0=0) n) gets type Set rather than Prop *)
(* Explains why I can use unit for the return type of head/tail's 0 case instead of True *)
Inductive Vect (A : Type) : nat -> Type := vnil : Vect A 0 | vcons : forall n : nat, A -> Vect A n -> Vect A (S n).
(* This stuff is just so I can make the type arguments implicit *)
Arguments vnil {A}.
Arguments vcons {A} {n} _ _.

Module VectNotes.
    Notation "[]" := vnil (at level 0) : vect_scope.
    Infix "::" := vcons (at level 60, right associativity) : vect_scope.
    Open Scope vect_scope.
    Notation "[ x ]" := ((x :: [])) (at level 0) : vect_scope.
    Notation "[ x , .. , y ]" := ((vcons x .. (y :: []) ..)) (at level 0) : vect_scope.
End VectNotes.
Import VectNotes.

Definition hdtype : Type -> nat -> Type
    :=  fun (A : Type) (n : nat) =>
        match n with
            | 0     => unit
            | S k   => A
        end.

Definition tltype : Type -> nat -> Type
    :=  fun (A : Type) (n : nat) =>
        match n with
            | 0     => unit
            | S k   => Vect A k
        end.

Definition head : forall {A : Type} {n : nat}, Vect A (S n) -> A
    :=  fun (A : Type) (n : nat) (v : Vect A (S n)) =>
        match v in (Vect _ m) return (hdtype A m) with
            | []        => tt
            | x :: xs   => x
        end.

Definition tail : forall {A : Type} {n : nat}, Vect A (S n) -> Vect A n
    :=  fun (A : Type) (n : nat) (v : Vect A (S n)) =>
        match v in (Vect _ m) return (tltype A m) with
            | []        => tt
            | x :: xs   => xs
        end.

(* Returns the last element of a non-empty vector *)
Fixpoint last {A : Type} {n : nat} : Vect A (S n) -> A
    :=  match n as k return (Vect A (S k) -> A) with
            | 0     => head (* last element of a singleton vector is also its head *)
            | S i   => fun v : Vect A (S (S i)) => last (tail v)
        end.

(*  note: this can also be defined by recursion on the vector argument (and probably more legibly so);
    However, in what I've done with these stuff so far, often times it's easier to prove theorems where vmap is involved
    by recursing on the nat (eg, to prove the monad laws, since mu [the diagonal] must be defined by recursion over nat) *)
Fixpoint vmap {A B : Type} {n : nat} (f : A -> B) : Vect A n -> Vect B n
    :=  match n as k return (Vect A k -> Vect B k) with
            | 0     =>  fun v : Vect A 0     => []
            | S i   =>  fun v : Vect A (S i) => (f (head v)) :: (vmap f (tail v))
        end.
(* alt version of vmap via recursion on v *)
(*  Fixpoint vmap' {A B : Type} {n : nat} (f : A -> B) (v : Vect A n) : Vect B n
        :=  match v in (Vect _ k) return (Vect B k) with
                | []        => []
                | x :: r    => (f x)::(vmap' f r)
            end. *)

Definition vcast : forall {A : Type} {m : nat}, Vect A m -> forall {n : nat}, m = n -> Vect A n
    := fun (A : Type) (m : nat) => eq_rect m (Vect A).

Fixpoint append {A : Type} {m n : nat} (u : Vect A m) (v : Vect A n) : Vect A (m+n)
    :=  match u in (Vect _ i) return (Vect A (i+n)) with
            | []        => v
            | x :: l    => x :: (append l v)
         end.
Infix "++" := append (at level 60, right associativity) : vect_scope.

(* Type of proofs that vector u is a subvector of vector v *)
Inductive subvect {A : Type} : forall {m n : nat}, Vect A m -> Vect A n -> Prop
    :=  vbot : subvect [] []
    |   con1 : forall {m n : nat} (u : Vect A m) (v : Vect A n) (x : A), subvect u v -> subvect u (x :: v)
    |   con2 : forall {m n : nat} (u : Vect A m) (v : Vect A n) (x : A), subvect u v -> subvect (x :: u) (x :: v).
Infix "isSubvectof" := subvect (at level 30) : type_scope.
Infix "⊑" := subvect (at level 30) : type_scope.

(* splits a term v:(Vect A (m+n)) into a pair (Vect A m)*(Vect A n) *)
Fixpoint vsplit_at {A : Type} (m n : nat) {struct m} : Vect A (m+n) -> (Vect A m)*(Vect A n)
    :=  match m as z return (Vect A (z+n) -> (Vect A z)*(Vect A n)) with
            | 0     => fun v : Vect A n => ([],v)
            | S i   => fun v : Vect A (S (i+n)) => let (l,r) := (vsplit_at i n (tail v)) in ((head v)::l,r)
                        (*  fun v : Vect A (S (i+n)) =>
                            prod_rect   (fun _ : (Vect A i)*(Vect A n) => ((Vect A (S i))*(Vect A n))%type)
                                        (fun xs : Vect A i => pair ((head v)::xs)) (v_split_at A i n (tail v)) *)
        end.

(* take & drop basically are the first and second projections of vsplit_at- hoping to make induction easier using them *)
Fixpoint take (A : Type) (m n : nat) {struct m} : Vect A (m+n) -> Vect A m
    :=  match m as k return (Vect A (k+n) -> Vect A k) with
            | 0     => fun _ : Vect A n => []
            | S i   => fun v : Vect A (S (i+n)) => (head v)::(take A i n (tail v))
        end.

Fixpoint drop (A : Type) (m n : nat) {struct m} : Vect A (m+n) -> Vect A n
    :=  match m as k return (Vect A (k+n) -> Vect A n) with
            | 0     => fun v : Vect A n => v
            | S i   => fun v : Vect A (S (i+n)) => drop A i n (tail v)
        end.
Arguments take {A} m {n} v.
Arguments drop {A} m {n} v.

Fixpoint nth {A : Type} (m : nat) {n : nat} : Vect A (S (m+n)) -> A
    :=  match m as k return (Vect A (S (k+n)) -> A) with
            | 0     => head
            | S i   => fun v : Vect A (S (S (i+n))) => nth i (tail v)
        end.
(* Fixpoint max (m n : nat) : nat
    :=  match m,n with
            | 0,j       => j
            | i,0       => i
            | S i,S j   => S (max i j)
        end. *)
Fixpoint max (m n : nat) : nat
    :=  match m with
            | 0     => n
            | S i   => S (match n with 0 => i | S j => max i j end)
        end.

(* removing induction in recursive cases *)
Fixpoint m_frnt (m n k : nat) {struct m} : {x : nat | ((max m n)+k) = (m+x)}
    :=  match m as i,n as j return {x : nat | ((max i j)+k) = (i+x)} with
            | 0,j       =>  exist (fun x : nat => (j+k) = x) (j+k) eq_refl
            | S i,0     =>  exist (fun x : nat => (S (i+k)) = (S (i+x))) k eq_refl
            | S i,S j   =>  exist (fun x : nat => (S ((max i j)+k)) = (S (i+x)))
                                  (proj1_sig (m_frnt i j k)) (f_equal S (proj2_sig (m_frnt i j k)))
        end.

Fixpoint n_frnt (m n k : nat) {struct m} : {y : nat | ((max m n)+k) = (n+y)}
    :=  match m as i,n as j return {y : nat | ((max i j)+k) = (j+y)} with
            | 0,j       =>  exist (fun y : nat => (j+k) = (j+y)) k eq_refl
            | S i,0     =>  exist (fun y : nat => (S (i+k)) = y) (S (i+k)) eq_refl
            | S i,S j   =>  exist (fun y : nat => (S ((max i j)+k)) = (S (j+y)))
                                  (proj1_sig (n_frnt i j k)) (f_equal S (proj2_sig (n_frnt i j k)))
        end.


Inductive HetVect : forall n : nat, Vect statterm n -> Set :=
    | hnil  : HetVect 0 []
    | hcons : forall {n : nat} {v : Vect statterm n} (s : statterm), (Sns s) -> (HetVect n v) -> (HetVect (S n) (s :: v)).

Fixpoint happend {m n : nat} {u : Vect statterm m} {v : Vect statterm n} (h : HetVect m u) (h' : HetVect n v)
    : HetVect (m + n) (u ++ v)
    :=  match h in (HetVect i l) return (HetVect (i + n) (l ++ v)) with
            | hnil          => h'
            (* had to change recently from "hcons i l s x r   => hcons s x (happend r h')"- huh? *)
            | hcons s x r   => hcons s x (happend r h')
        end.
Infix "+++" := happend (at level 60, right associativity).

(* Type of proofs that HetVect m h is a subHetVect of HetVect n k *)
Inductive subhetvect : forall {m n : nat} {u : Vect statterm m} {v : Vect statterm n}, HetVect m u -> HetVect n v -> Prop
    :=  hbot    : subhetvect hnil hnil
    |   hcon1   : forall {m n : nat} {u : Vect statterm m} {v : Vect statterm n} (h : HetVect m u) (k : HetVect n v)
                            (s : statterm) (x : (Sns s)), subhetvect h k -> subhetvect h (hcons s x k)
    |   hcon2   : forall {m n : nat} {u : Vect statterm m} {v : Vect statterm n} (h : HetVect m u) (k : HetVect n v)
                            (s : statterm) (x : (Sns s)), subhetvect h k -> subhetvect (hcons s x h) (hcons s x k).
Infix "isSubHetVectof" := subhetvect (at level 30) : type_scope.

Fixpoint hexists {n : nat} {v : Vect statterm n} : (HetVect n v -> prop) -> prop
    :=  match v as u in (Vect _ k) return ((HetVect k u -> prop) -> prop) with
            | []                =>  fun P : HetVect 0 [] -> prop => P hnil
            (* more changes needing to do b/c syntax changed? *)
            | @vcons _ i s r    =>  fun P : HetVect (S i) (s::r) -> prop =>
                                    p_exists s (fun x : Sns s => hexists (fun h : HetVect i r => P (hcons s x h)))
        end.

Fixpoint hforall {n : nat} {v : Vect statterm n} : (HetVect n v -> prop) -> prop
    :=  match v as u in (Vect _ k) return ((HetVect k u -> prop) -> prop) with
            | []                =>  fun P : HetVect 0 [] -> prop => P hnil
            (* another change needing to make b/c syntax change *)
            | @vcons _ i s r    =>  fun P : HetVect (S i) (s::r) -> prop =>
                                    p_forall s (fun x : Sns s => hforall (fun h : HetVect i r => P (hcons s x h)))
        end.

Definition hethead : forall {m : nat} {v : Vect statterm (S m)}, HetVect (S m) v -> Sns (head v)
    :=  fun (m : nat) (v : Vect statterm (S m)) (h : HetVect (S m) v) =>
        match h in (HetVect k u)
        return ((match k as n return (Vect statterm n -> Type) with
                    | 0     => fun _ : Vect statterm 0 => unit
                    | S i   => fun l : Vect statterm (S i) => Sns (head l)
                 end) u)
        with hnil => tt | hcons _ x _ => x end.
Definition hettail : forall {m : nat} {v : Vect statterm (S m)}, HetVect (S m) v -> HetVect m (tail v)
    :=  fun (m : nat) (v : Vect statterm (S m)) (h : HetVect (S m) v) =>
        match h in (HetVect k u)
        return ((match k as n return (Vect statterm n -> Type) with
                    | 0     => fun _ : Vect statterm 0 => unit
                    | S i   => fun l : Vect statterm (S i) => HetVect i (tail l)
                 end) u)
        with hnil => tt | hcons _ _ r => r end.

(* same as vsplit_at, but for HetVects *)
Fixpoint hsplit_at (m n : nat) (u : Vect statterm m) (v : Vect statterm n) : HetVect (m+n) (u++v) -> (HetVect m u)*(HetVect n v)
    :=  match u as l in (Vect _ k) return (HetVect (k+n) (l ++ v) -> (HetVect k l)*(HetVect n v)) with
            | []                =>  pair hnil
            | @vcons _ i s l    =>  fun h : HetVect (S (i+n)) (s::(l ++ v)) =>
                                    let (xs,ys) := (hsplit_at i n l v (hettail h)) in (hcons s (hethead h) xs,ys)
        end.

(* Fixpoint hsplit_at {m n : nat} {u : Vect statterm m} {v : Vect statterm n} : HetVect (m+n) (u++v)->(HetVect m u)*(HetVect n v)
    :=  match u as l in (Vect _ k) return (HetVect (k + n) (l ++ v) -> (HetVect k l)*(HetVect n v)) with
            | []                =>  fun h : HetVect n v => (hnil,h)
            | @vcons _ i s l    =>  fun h : HetVect (S (i + n)) (s::(l ++ v)) =>
                                    (match h in (HetVect j r)
                                     return (match r with
                                                | []                => unit
                                                | @vcons _ k t ts   => (HetVect k ts -> (HetVect i l)*(HetVect n v))
                                                                            -> (HetVect (S i) (t::l))*(HetVect n v)
                                             end) with
                                        | hnil              =>  tt
                                        | @hcons j r t x w  =>  fun f : HetVect j r -> (HetVect i l)*(HetVect n v) =>
                                                                let (h1,h2) := (f w) in (hcons t x h1,h2)
                                     end)
                                    (@hsplit_at i n l v)
        end. *)
(* Proofs (to be given their own file) *)

    (* every 0-length vector is [], every (S i)-length vector is defined as its head cons'ed onto its tail *)
    Definition vfrmtyp : forall (A : Type) (k : nat), Vect A k -> Prop
        :=  fun (A : Type) (k : nat) =>
            match k as m return (Vect A m -> Prop) with
                | 0     => fun u : Vect A 0 => [] = u
                | S i   => fun u : Vect A (S i) => ((head u)::(tail u)) = u
            end.

    Definition Vect_form : forall {A : Type} {n : nat} (v : Vect A n), vfrmtyp A n v
        :=  fun (A : Type) (n : nat) (v : Vect A n) =>
            match v as u in (Vect _ k) return (vfrmtyp A k u) with
                | []    => eq_refl
                | x::xs => eq_refl
            end.

    (* Functor Laws for vmap, starting by defining identity function (id) and composition (comp/∘) *)
    Definition id : forall {A : Type}, A -> A := fun (A : Type) (x : A) => x.
    Definition comp : forall {A B C:Type},(B->C)->(A->B)->A->C := fun (A B C : Type) (f : B -> C) (g : A -> B) (x : A) => f (g x).
    Infix "∘" := comp (at level 20).

    Definition funct1 : forall (A : Type) (n : nat) (v : Vect A n), (vmap id v) = v
        :=  fun A : Type => Vect_ind A  (fun (n : nat) (v : Vect A n) => (vmap id v) = v) eq_refl
                                        (fun (i : nat) (x : A) (r : Vect A i) (e : (vmap id r) = r) => f_equal (vcons x) e).

    Definition funct2 : forall (A B C : Type) (f : B -> C) (g : A -> B) (n : nat) (v : Vect A n),(vmap f (vmap g v))=(vmap (f∘g) v)
        :=  fun (A B C : Type) (f : B -> C) (g : A -> B) =>
            Vect_ind A  (fun (n : nat) (v : Vect A n) => (vmap f (vmap g v)) = (vmap (f∘g) v)) eq_refl
                        (fun (i : nat) (x : A) (r : Vect A i) (e : (vmap f (vmap g r)) = (vmap (f∘g) r)) =>
                            f_equal (vcons (f (g x))) e).

    Definition vspl_app_inv : forall {A : Type}{m n : nat} (v : Vect A (m+n)), v=((fst (vsplit_at m n v))++(snd (vsplit_at m n v)))
        :=  fun A : Type =>
            nat_ind (fun m : nat => forall (n : nat) (v : Vect A (m+n)), v = ((fst (vsplit_at m n v)) ++ (snd (vsplit_at m n v))))
                    (fun (n : nat) (v : Vect A n) => eq_refl)
                    (fun (i : nat) (f : forall (n : nat) (v : Vect A (i+n)), v = ((fst (vsplit_at i n v)) ++ (snd (vsplit_at i n v))))
                         (n : nat) (v : Vect A (S (i+n))) =>
                       eq_ind   ((head v)::(tail v))
                                (fun u : Vect A (S (i+n)) => u = ((fst (vsplit_at (S i) n u)) ++ (snd (vsplit_at (S i) n u))))
                                (eq_ind ((head v)::(fst (vsplit_at i n (tail v))),snd (vsplit_at i n (tail v)))
                                        (fun p : (Vect A (S i))*(Vect A n) => ((head v)::(tail v)) = ((fst p) ++ (snd p)))
                                        (f_equal (vcons (head v)) (f n (tail v)))
                                        (let (l,r) := (vsplit_at i n (tail v)) in ((head v)::l,r))
                                        (prod_ind   (fun p : (Vect A i)*(Vect A n) => ((head v)::(fst p),snd p)
                                                            = (let (l,r) := p in ((head v)::l,r)))
                                                    (fun (l : Vect A i) (r : Vect A n) => eq_refl)
                                                    (vsplit_at i n (tail v))))
                                v
                                (Vect_form v)).

    (* A version of eq_ind for proving facts about equality proofs themselves *)
    Definition eq_ind_dep : forall {A:Type} (x:A) (P:forall z:A, x = z -> Prop), P x eq_refl -> forall (y:A) (e:x=y), P y e
        :=  fun (A : Type) (x : A) (P : forall z : A, x = z -> Prop) (p : P x eq_refl) (y : A) (e : x = y) =>
            match e as d in (_ = z) return (P z d) with eq_refl => p end.

    (* Associativity of (++), starting with a proof of the associativity of (+) *)
    Fixpoint add_assoc (m n p : nat) {struct m} : ((m+n)+p) = (m+(n+p))
        := match m as i return (((i+n)+p) = (i+(n+p))) with 0 => eq_refl | S i => f_equal S (add_assoc i n p) end.

    Definition app_assoc : forall {A : Type} {m n p : nat} (u : Vect A m) (v : Vect A n) (w : Vect A p),
        (eq_rect ((m+n)+p) (Vect A) ((u++v)++w) (m+(n+p)) (add_assoc m n p)) = (u++(v++w))
        :=  fun (A : Type) (m n p : nat) (u : Vect A m) (v : Vect A n) (w : Vect A p) =>
            Vect_ind A
                (fun (i : nat) (r : Vect A i) => (eq_rect ((i+n)+p) (Vect A) ((r++v)++w) (i+(n+p)) (add_assoc i n p)) = (r++(v++w)))
                eq_refl
                (fun (i : nat) (x : A) (r : Vect A i)
                     (e : (eq_rect ((i+n)+p) (Vect A) ((r++v)++w) (i+(n+p)) (add_assoc i n p)) = (r++(v++w))) =>
                     eq_trans   (eq_ind_dep ((i+n)+p)
                                    (fun (z : nat) (d : ((i+n)+p) = z) =>
                                        (eq_rect (S ((i+n)+p)) (Vect A) (x::((r++v)++w)) (S z) (f_equal S d))
                                            = (x::(eq_rect ((i+n)+p) (Vect A) ((r++v)++w) z d)))
                                    eq_refl (i+(n+p)) (add_assoc i n p))
                                (f_equal (vcons x) e))
                m u.

    Definition tkdr_app_inv : forall {A : Type} (m : nat) {n : nat} (v : Vect A (m+n)), v = ((take m v) ++ (drop m v))
        :=  fun (A : Type) (m n : nat) =>
            nat_ind (fun i : nat => forall v : Vect A (i+n), v = ((take i v) ++ (drop i v)))
                    (@eq_refl (Vect A n))
                    (fun (i : nat) (f : forall r : Vect A (i+n), r = ((take i r) ++ (drop i r))) (v : Vect A (S (i+n))) =>
                        eq_trans (eq_sym (Vect_form v)) (f_equal (vcons (head v)) (f (tail v)))) m.

    (* take/drop of a vector (l++r) is equal to l/r, respectively *)
    Definition tkdr_app_inv2a : forall {A : Type} (m : nat) {n : nat} (u : Vect A m) (v : Vect A n), u = (take m (u++v))
        :=  fun (A : Type) (m n : nat) (u : Vect A m) (v : Vect A n) =>
            Vect_ind A  (fun (i : nat) (l : Vect A i) => l = (take i (l ++ v))) eq_refl
                        (fun (i : nat) (x : A) (l : Vect A i) (e : l = (take i (l ++ v))) => f_equal (vcons x) e) m u.
    Definition tkdr_app_inv2b : forall {A : Type} (m : nat) {n : nat} (u : Vect A m) (v : Vect A n), v = (drop m (u++v))
        :=  fun (A : Type) (m n : nat) (u : Vect A m) (v : Vect A n) =>
            Vect_ind A  (fun (i : nat) (l : Vect A i) => v = (drop i (l ++ v))) eq_refl
                        (fun (i : nat) (_ : A) (l : Vect A i) (e : v = (drop i (l ++ v))) => e) m u.

    Definition drop_assoc : forall {A : Type} (m n k : nat) (v : Vect A ((m+n)+k)),
        (drop (m+n) v) = (drop n (drop m (vcast v (add_assoc m n k))))
        :=  fun (A : Type) (m n k : nat) =>
            nat_ind (fun i : nat => forall v : Vect A ((i+n)+k), (drop (i+n) v) = (drop n (drop i (vcast v (add_assoc i n k)))))
                    (fun v : Vect A (n+k) => eq_refl)
                    (fun (i : nat) (f : forall v : Vect A ((i+n)+k), (drop (i+n) v) = (drop n (drop i (vcast v (add_assoc i n k)))))
                         (v : Vect A (S ((i+n)+k))) =>
                        eq_trans    (f (tail v))
                                    (f_equal    (fun u : Vect A (i+(n+k)) => (drop n (drop i u)))
                                                (eq_ind_dep ((i+n)+k)
                                                            (fun (z : nat) (d : ((i+n)+k) = z) =>
                                                                (vcast (tail v) d) = (tail (vcast v (f_equal S d))))
                                                            eq_refl (i+(n+k)) (add_assoc i n k))))
                    m.

    (* Proof that hnil is a subvect of all HetVects *)
    Definition hnil_bot : forall {n : nat} {v : Vect statterm n} (h : HetVect n v), hnil isSubHetVectof h
        :=  HetVect_ind (fun (n : nat) (v : Vect statterm n) (h : HetVect n v) => hnil isSubHetVectof h)
                        hbot
                        (fun (i : nat) (r : Vect statterm i) (s : statterm) (x : Sns s) (u : HetVect i r) => hcon1 hnil u s x).

