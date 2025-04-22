Require Import Nat.
Require Import Ensembles.
Require Import Coq.Arith.EqNat.
Require Import Coq.Logic.Classical.
Require Import IndefiniteDescription.

Arguments Singleton {U}.
Arguments Empty_set {U}.
Arguments Full_set {U}. 
Arguments Union {U}. 
Arguments Intersection {U}. 
Arguments In {U}. 
Arguments Included {U}.
Arguments Complement {U}. 

Inductive formula {Act : Type} : Type :=
  | tt : formula
  | ff : formula
  | var : nat -> formula
  | neg : formula -> formula
  | and : formula -> formula -> formula 
  | or : formula -> formula -> formula
  | box : Act -> formula -> formula
  | diamond : Act -> formula -> formula
  | nu : formula -> formula
  | mu : formula -> formula.

Check nu (var 0).

Record lts {Act : Type} : Type :=
  { state : Type
  ; transition : state -> Act -> state -> Prop 
  ; initial : state -> Prop}.

Definition env {Act : Type} {M : (@lts Act)} := (nat -> (Ensemble (state M))).

Definition newenvironment {U : Type} (e : nat -> (Ensemble U)) (S : (Ensemble U)) : nat -> (Ensemble U) :=
fun n: nat =>
match n with 
| 0 => S
| S n => e n
end.

Fixpoint formulasemantics {Act : Type} (f : formula) (M : (@lts Act)) (e : env) : Ensemble (state M) :=
  match f with
  | tt => Full_set
  | ff => Empty_set
  | var X => e X
  | neg f' => Complement (formulasemantics f' M e)
  | and f' f'' => Intersection (formulasemantics f' M e) (formulasemantics f'' M e)
  | or f' f'' => Union (formulasemantics f' M e) (formulasemantics f'' M e)
  | box act f' => fun s : (state M) => forall s' : (state M), (((In (formulasemantics f' M e) s')) -> ((transition M) s act s'))
  | diamond act f' => fun s : (state M) => exists s' : (state M), (((transition M) s act s') /\ (In (formulasemantics f' M e) s'))
  | nu f' => fun s =>  exists S', (Included S' (formulasemantics f' M (newenvironment e S'))) /\ (In S' s) 
  | mu f' => fun s =>  forall S', ((Included (formulasemantics f' M (newenvironment e S')) S') -> (In S' s))
  end.

Definition path {Act : Type} (M : (@lts Act)) := nat -> (state M).

Definition validpath {Act : Type} (M : (@lts Act)) (p : (path M)) : Prop :=
forall n : nat, (exists act: Act, ((transition M) (p n) act (p (S n)))). 

Definition validactionpath {Act : Type} {M : (@lts Act)} (p : (path M)) (act : Act) : Prop :=
forall n : nat, ((transition M) (p n) act (p (S n))).

Lemma and_semantics_correctness: forall (Act : Type) (f1 f2 : formula) (M : (@lts Act)) 
(e : env) (act : Act) (s : (state M)), 
In (formulasemantics (and f1 f2) M e) s <-> (In (formulasemantics f1 M e) s) /\ (In (formulasemantics f2 M e) s).
Proof.
split; intros.
simpl formulasemantics in H.
inversion H.
auto.
simpl formulasemantics;
apply Intersection_intro; intuition.
Qed. 

Lemma nuX_X : forall (Act : Type) (M : (@lts Act)) (e : env), Same_set (state M) (formulasemantics (nu (var 0)) M e) Full_set.
Proof.
intros.
unfold Same_set.
split; unfold Included; intros.
apply Full_intro.
unfold formulasemantics.
unfold In.
intros.
unfold newenvironment.
unfold Included.
exists (Full_set).
split;
intros;
apply Full_intro.
Qed.

Print Assumptions nuX_X.

Lemma choice' (A B : Type) (R : A -> B -> Prop) (H : (forall x : A, exists y : B, R x y)) : A -> B.
Proof.
  intros.
  destruct (constructive_indefinite_description _ (H X)).
  auto.
Defined. 

Lemma choice: forall (A B : Type) (R : A -> B -> Prop),
       (forall x : A, exists y : B, R x y) -> exists f : A -> B, forall x : A, R x (f x).
Proof.
intros.
exists (choice' A B R H).
unfold choice'.
intros x.
destruct constructive_indefinite_description.
auto.
Qed.

Lemma inbetweenlemma : forall (Act : Type) (M : (@lts Act))
(act : Act) (s : (state M)) (x : (Ensemble (state M))),
(In x s /\ (exists succ: state M -> state M, forall x': state M, 
In x x' -> ((transition M) x' act (succ x')) /\ (In x (succ x'))))
-> (exists p : path M,
  (forall n : nat, (transition M (p n) act (p (S n))) /\ In x (p  n)) /\ p 0 = s).
Proof.
intros.
destruct H.
destruct H0.
exists 
(fix path n :=
    match n with
    | 0 => s
    | S n' => x0 (path n')
    end
).
intros.
split.
induction n.
simpl.
split; try apply H0; intuition.
simpl.
split.
apply H0.
apply H0.
apply IHn.
apply H0.
intuition.
reflexivity.
Qed.

Lemma inbetweenlemma2 : forall (Act : Type) (M : (@lts Act))
(act : Act) (s : (state M)) (x : (Ensemble (state M))),
(In x s /\ (exists succ: state M -> state M, forall x': state M, 
In x x' -> ((transition M) x' act (succ x')) /\ (In x (succ x'))))
-> (exists p : nat -> state M,
  (forall n : nat, (transition M (p n) act (p (S n)))) /\ p 0 = s).
Proof.
intros.
specialize (inbetweenlemma Act M act s x).
intros.
intuition.
destruct H.
exists x0.
destruct H.
split.
intro n.
destruct (H n).
intuition.
apply H0.
Qed.

Lemma nuX_diamondactX_ltr : forall (Act : Type) (M : (@lts Act)) (e : env)
(act : Act) (s : (state M)),
(In (formulasemantics (nu (diamond act (var 0))) M e) s) -> (exists (p : path M), (validactionpath p act) /\ (p 0 = s)).
Proof.
intros.
unfold formulasemantics in H.
unfold newenvironment in H.
unfold In in H.
destruct H.
apply inbetweenlemma2 with (x := x).
split; intuition.
apply choice with 
(R := fun x' s' => ((In x x') ->(transition M x' act s') /\ In x s')).
intro.
destruct (classic (In x x0)).
destruct (H0 x0).
exact H.
exists x1.
intro.
exact H2.
exists x0.
intro.
contradiction.
Qed.

Lemma nuX_diamondactX_rtl : forall (Act : Type) (X : nat) (M : (@lts Act)) (e : env)
(act : Act) (s : (state M)),
(exists (p : path M), ((validactionpath p act)) /\ p 0 = s) -> 
  (In (formulasemantics (nu (diamond act (var 0))) M e) s).
Proof.
simpl.
unfold In at 1, Included, In at 3.
intros.
destruct H.
unfold validactionpath in H.
exists (fun (s' : (state M)) => (exists n : nat, x n = s')); unfold In.
intuition.
destruct H.
exists (x (S x1)).
intuition.
rewrite <- H.
apply H0.
exists (S x1).
intuition.
exists 0.
auto.
Qed.

Lemma nuX_diamondactX : forall (Act : Type) (X : nat) (M : (@lts Act)) (e : env)
(act : Act) (s : (state M)),
(In (formulasemantics (nu (diamond act (var 0))) M e) s) <->
  (exists path : path M, validactionpath path act /\ path 0 = s).
Proof.
intuition; 
try apply nuX_diamondactX_ltr with (e := e); auto.
try apply nuX_diamondactX_rtl; auto.
Qed. 

Print Assumptions nuX_diamondactX.

Fixpoint negvari {Act : Type} (f : @formula Act) (i : nat) : @formula Act :=
match f with
  | tt => tt
  | ff => ff
  | var X => if (Nat.eqb X i) then (neg (var X)) else (var X)
  | neg f => neg (negvari f i)
  | and f f' => and (negvari f i) (negvari f' i)
  | or f f' => or (negvari f i) (negvari f' i)
  | box act f => box act (negvari f i)
  | diamond act f => diamond act (negvari f i)
  | nu f => nu (negvari f (S i))
  | mu f => mu (negvari f (S i))
  end.