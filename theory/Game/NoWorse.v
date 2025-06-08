Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Strategy.
Require Import Games.Game.Win.

(* the player p can at least draw.
   classically, we'd say that they draw or win,
   but this "or" is constructively dubious *)
CoInductive no_worse {G : Game} (p : Player) : GameState G -> Type :=
  | atom_draw_no_worse : forall s,
      atomic_res s = Some Draw ->
      no_worse p s
  | atom_win_no_worse : forall s,
      atomic_res s = Some (Win p) ->
      no_worse p s
  | eloise_no_worse : forall s,
      to_play s = p ->
      atomic_res s = None ->
      forall m, no_worse p (exec_move s m) ->
      no_worse p s
  | abelard_no_worse : forall s,
      to_play s = opp p ->
      atomic_res s = None ->
      (forall m, no_worse p (exec_move s m)) ->
      no_worse p s.

Fixpoint win_no_worse {G : Game} p (s : GameState G) (w : win p s) : no_worse p s.
Proof.
  destruct w.
  - apply atom_win_no_worse.
    exact e.
  - eapply eloise_no_worse; auto.
    apply win_no_worse.
    exact w.
  - apply abelard_no_worse; auto.
Defined.

Lemma no_worse_not_loss {G : Game}
  (p : Player) (s : GameState G) :
  no_worse p s -> win (opp p) s -> False.
Proof.
  intros n w.
  induction w.
  - destruct n; try congruence.
    elim (opp_no_fp p); congruence.
  - destruct n; try congruence.
    + elim (opp_no_fp p); congruence.
    + auto.
  - destruct n; try congruence.
    + apply (H m); auto.
    + elim (opp_no_fp (opp p)); congruence.
Qed.

CoFixpoint strategy_of_no_worse {G : Game} {p : Player} {s : GameState G}
  (n : no_worse p s) : strategy p s.
Proof.
  destruct n.
  - eapply atom_strategy.
    exact e.
  - eapply atom_strategy.
    exact e.
  - eapply eloise_strategy; auto.
    apply strategy_of_no_worse.
    exact n.
  - eapply abelard_strategy; auto.
Defined.

CoFixpoint strategy_of_no_worse_correct {G : Game} {p : Player} (s : GameState G)
  (n : no_worse p s) : no_worse_strategy p (strategy_of_no_worse n).
Proof.
  rewrite (strat_id_eq _).
  unfold strat_id.
  destruct n.
  - unfold strategy_of_no_worse.
    constructor.
  - unfold strategy_of_no_worse.
    constructor.
  - unfold strategy_of_no_worse.
    constructor.
    apply strategy_of_no_worse_correct.
  - unfold strategy_of_no_worse.
    constructor.
    intro.
    apply strategy_of_no_worse_correct.
Qed.

Record trap {G : Game} (p : Player) (P : GameState G -> Type) : Type := {
  trap_eloise : forall s,
    P s ->
    to_play s = p ->
    atomic_res s = None -> { m : Move s & P (exec_move s m) };
  trap_abelard : forall s,
    P s ->
    to_play s = opp p ->
    atomic_res s = None -> forall m, P (exec_move s m);
  opp_wins_disjoint : forall s, P s -> atomic_res s <> Some (Win (opp p))
  }.

Arguments trap_eloise {_} {_} {_} _ _.
Arguments trap_abelard {_} {_} {_} _ _.
Arguments opp_wins_disjoint {_} {_} {_} _ _.

CoFixpoint trap_no_worse {G} p (P : GameState G -> Type) (tr : trap p P) : forall s,
  P s -> no_worse p s.
Proof.
  intros s Hs.
  destruct (atomic_res s) as [[p'|]|] eqn:s_res.
  - destruct (player_id_or_opp_r_t p' p); subst.
    + apply atom_win_no_worse; auto.
    + elim (opp_wins_disjoint tr s); auto.
  - apply atom_draw_no_worse; auto.
  - destruct (player_id_or_opp_r_t (to_play s) p).
    + destruct (trap_eloise tr s Hs e s_res) as [m Hm].
      apply eloise_no_worse with (m := m); auto.
      eapply trap_no_worse; [exact tr|].
      exact Hm.
    + apply abelard_no_worse; auto.
      intro m.
      eapply trap_no_worse; [exact tr|].
      apply (trap_abelard tr s); auto.
Defined.

