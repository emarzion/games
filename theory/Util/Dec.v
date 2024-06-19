Require Compare_dec.
Require Import List.

Definition decision (P : Prop) : Type :=
  {P} + {~P}.

Class Discrete (X : Type) := {
  eq_dec : forall x x' : X, decision (x = x')
  }.

Global Instance prod_Discrete {X Y} `{Discrete X, Discrete Y} : Discrete (X * Y).
Proof.
  constructor; unfold decision; decide equality; apply eq_dec.
Defined.

Global Instance option_Discrete {X} `{Discrete X} : Discrete (option X).
Proof.
  constructor; unfold decision; decide equality; apply eq_dec.
Defined.

Global Instance nat_Discrete : Discrete nat.
Proof.
  constructor.
  apply PeanoNat.Nat.eq_dec.
Defined.

Class Exhaustible (X : Type) := {
  sig_dec : forall (P : X -> Prop),
    (forall x, decision (P x)) ->
    decision (exists x, P x)
  }.

Global Instance prod_Exhaustible (X Y : Type)
  `{Exhaustible X, Exhaustible Y}
  : Exhaustible (X * Y).
Proof.
  constructor.
  intros P Pd.
  destruct (sig_dec (fun x => exists y, P (x, y))).
  - intro x.
    destruct (sig_dec (fun y => P (x, y))).
    + intro; apply Pd.
    + left; auto.
    + right; auto.
  - left.
    destruct e as [x [y Hxy]].
    exists (x, y); exact Hxy.
  - right; intros [[x y] Hxy].
    apply n; exists x, y; exact Hxy.
Defined.

Class Dec (P : Prop) := {
  dec : {P} + {~P}
  }.

Global Instance true_Dec : Dec True.
Proof.
  constructor.
  left; exact I.
Defined.

Global Instance false_Dec : Dec False.
Proof.
  constructor.
  right; exact (fun e => e).
Defined.

Global Instance impl_Dec {P Q} `{Dec P, Dec Q} : Dec (P -> Q).
Proof.
  constructor.
  destruct (dec (P := P)); [|tauto].
  destruct (dec (P := Q)); tauto.
Defined.

Global Instance and_Dec {P Q} `{Dec P, Dec Q} : Dec (P /\ Q).
Proof.
  constructor.
  destruct (dec (P := P)); [|tauto].
  destruct (dec (P := Q)); tauto.
Defined.

Global Instance or_Dec {P Q} `{Dec P, Dec Q} : Dec (P \/ Q).
Proof.
  constructor.
  destruct (dec (P := P)); [tauto|].
  destruct (dec (P := Q)); tauto.
Defined.

Global Instance le_Dec : forall m n, Dec (m <= n).
Proof.
  intros.
  constructor.
  apply Compare_dec.le_dec.
Defined.

Global Instance lt_Dec : forall m n, Dec (m < n).
Proof.
  intros.
  constructor.
  apply Compare_dec.lt_dec.
Defined.

Global Instance Discrete_Eq_Dec {X} `{Discrete X} : forall {x x' : X}, Dec (x = x').
Proof.
  intros; constructor; apply eq_dec.
Defined.

Global Instance Exhaustible_Sig_Dec {X} `{Exhaustible X} {P : X -> Prop} `{forall x, Dec (P x)}
 : Dec (exists x, P x).
Proof.
  constructor.
  apply sig_dec.
  intro; apply dec; auto.
Defined.

Global Instance Exhaustible_Pi_Dec {X} `{Exhaustible X} {P : X -> Prop} `{forall x, Dec (P x)}
  : Dec (forall x, P x).
Proof.
  constructor.
  destruct (sig_dec (fun x => ~ (P x))) as [|HPx].
  - intro; destruct (dec (P := P x)) as [|HPx].
    + right; tauto.
    + left; auto.
  - right; firstorder.
  - left; intro x.
    destruct (dec (P := P x)); [auto|].
    elim HPx.
    exists x; auto.
Defined.

Lemma in_dec {X} `{Discrete X} (x : X) (xs : list X) :
  { In x xs } + { ~ In x xs }.
Proof.
  induction xs as [|x' xs']; simpl.
  - now right.
  - destruct (eq_dec x' x).
    + left; now left.
    + destruct IHxs'.
      * left; now right.
      * right; intros [|]; contradiction.
Defined.

Definition in_decb {X} `{Discrete X} (x : X) (xs : list X) : bool :=
  match in_dec x xs with
  | left _ => true
  | right _ => false
  end.
