Require Import Games.Game.Player.
Require Import Games.Game.Game.
Require Import Games.Game.NoWorse.
Require Import Games.Game.Strategy.

CoInductive holds {G : Game} (p : Player) (P : GameState G -> Type)
  : GameState G -> Type :=
  | atom_holds : forall b o,
      atomic_res b = Some o ->
      P b -> holds p P b
  | eloise_holds : forall b, to_play b = p ->
      atomic_res b = None ->
      P b ->
      forall m, holds p P (exec_move b m) ->
      holds p P b
  | abelard_holds : forall b, to_play b = opp p ->
      atomic_res b = None ->
      P b ->
      (forall m, holds p P (exec_move b m)) ->
      holds p P b.

Definition acont {G} : GameState G -> Prop :=
  fun b => atomic_res b = None.

CoFixpoint holds_map {G : Game} (p : Player) (P Q : GameState G -> Type)
  (HPQ : forall s, P s -> Q s) : forall s, holds p P s -> holds p Q s.
Proof.
  intros s s_P.
  destruct s_P.
  - eapply atom_holds; eauto.
  - eapply eloise_holds; eauto.
  - apply abelard_holds; auto.
    intro m.
    eapply holds_map; eauto.
Defined.

CoFixpoint holds_no_worse {G : Game} (p : Player) (b : GameState G)
  : holds p acont b -> no_worse p b.
Proof.
  intro hold.
  destruct hold.
  - unfold acont in a.
    congruence.
  - apply eloise_no_worse with (m := m); auto.
  - apply abelard_no_worse; auto.
Defined.
