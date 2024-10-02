Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Strategy.
Require Import Games.Game.Win.
Require Import Games.Game.NoWorse.

CoInductive draw {G : Game} : GameState G -> Type :=
  | atom_draw : forall s,
      (* stalemate *)
      atomic_res s = Some Draw ->
      draw s
  | play_draw : forall s p,
      to_play s = p ->
      (* ongoing *)
      atomic_res s = None ->
      (* opponent at least draws for any move current player makes *)
      (forall m, no_worse (opp p) (exec_move s m)) ->
      (* there is a move that draws *)
      forall m, draw (exec_move s m) ->
      draw s.

Lemma win_not_draw {G : Game} : forall (p : Player) (s : GameState G),
  win p s -> draw s -> False.
Proof.
  intros p s w.
  induction w; intro d.
  - destruct d; congruence.
  - destruct d; try congruence.
    specialize (n m).
    elim (no_worse_not_loss (opp p0) (exec_move s m)); auto.
    rewrite opp_invol; congruence.
  - destruct d; try congruence.
    exact (H m d).
Qed.

CoFixpoint draw_no_worse {G : Game} : forall (p : Player) (s : GameState G),
  draw s -> no_worse p s.
Proof.
  intros p s d.
  destruct d.
  - apply atom_draw_no_worse.
    exact e.
  - destruct (player_id_or_opp_r_t (to_play s) p).
    + eapply eloise_no_worse; auto.
      apply draw_no_worse.
      exact d.
    + apply abelard_no_worse; auto.
      intro m'.
      rewrite e in e1.
      rewrite e1 in n.
      rewrite opp_invol in n.
      apply n.
Defined.

CoFixpoint both_no_worse_draw {G : Game} p (s : GameState G) :
  no_worse p s -> no_worse (opp p) s -> draw s.
Proof.
  intros n n'.
  destruct n.
  - apply atom_draw; auto.
  - destruct n'; try congruence.
    elim (opp_no_fp p); congruence.
  - destruct n'; try congruence.
    + elim (opp_no_fp p); congruence.
    + eapply play_draw with (p := p); auto.
      eapply both_no_worse_draw.
      * exact n.
      * apply n0.
  - destruct n'; try congruence.
    + eapply play_draw with (p := opp p); auto.
      * rewrite opp_invol; auto.
      * eapply both_no_worse_draw.
        -- exact n'.
        -- rewrite opp_invol.
           apply n.
    + elim (opp_no_fp (opp p)); congruence.
Defined.

CoFixpoint strategy_of_draw {G : Game} {p : Player} {s : GameState G}
  (d : draw s) : strategy p s.
Proof.
  destruct d.
  - exact (atom_strategy e).
  - destruct (player_id_or_opp_r_t (to_play s) p).
    + eapply eloise_strategy.
      * exact e0.
      * exact e1.
      * eapply strategy_of_draw.
        exact d.
    + eapply (abelard_strategy).
      * exact e0.
      * exact e1.
      * intro m'.
        apply strategy_of_no_worse.
        rewrite <- e in n.
        rewrite e1 in n.
        rewrite opp_invol in n.
        exact (n m').
Defined.

CoFixpoint strategy_of_draw_correct {G : Game} {p : Player} (s : GameState G)
  (d : draw s) : drawing_strategy p (strategy_of_draw d).
Proof.
  rewrite (strat_id_eq _).
  unfold strat_id.
  destruct d.
  - unfold strategy_of_draw.
    constructor.
  - unfold strategy_of_draw.
    destruct (player_id_or_opp_r_t (to_play s) p).
    + constructor.
      apply strategy_of_draw_correct.
    + constructor.
      intro.
      apply strategy_of_no_worse_correct.
Qed.
