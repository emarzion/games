Require Import Games.Game.Player.
Require Import Games.Game.Game.
Require Import Games.Game.Win.

Inductive forces {G : Game} (p : Player) (P : GameState G -> Prop)
  : GameState G -> Type :=
  | atom_force : forall b, P b -> forces p P b
  | eloise_force : forall b, to_play b = p ->
      atomic_res b = None ->
      forall m, forces p P (exec_move b m) ->
      forces p P b
  | abelard_force : forall b, to_play b = opp p ->
      atomic_res b = None ->
      (forall m, forces p P (exec_move b m)) ->
      forces p P b.

Definition awin {G} : Player -> GameState G -> Prop :=
  fun p b => atomic_res b = Some (Win p).

Definition forces_win {G : Game} (p : Player) (b : GameState G)
  : forces p (awin p) b -> win p b.
Proof.
  intro bf.
  induction bf.
  - apply atom_win; auto.
  - eapply eloise_win; eauto.
  - apply abelard_win; auto.
Defined.

Definition pforces {G : Game} (p : Player) (P Q : GameState G -> Prop) : Type :=
  forall b, P b -> forces p Q b.

Definition pforces_win {G : Game} : forall p (P : GameState G -> Prop),
  pforces p P (awin p) -> forall b, P b -> win p b.
Proof.
  intros.
  apply forces_win.
  apply X.
  auto.
Defined.

Definition pforces_trans {G} (p : Player) : forall (P Q R : GameState G -> Prop),
  pforces p P Q -> pforces p Q R -> pforces p P R.
Proof.
  intros P Q R fPQ fQR b Hb.
  pose proof (fPQ b Hb) as bfQ.
  clear fPQ.
  clear Hb.
  induction bfQ.
  - apply fQR; exact p0.
  - eapply eloise_force; auto.
    eapply IHbfQ.
  - eapply abelard_force; auto.
Defined.
