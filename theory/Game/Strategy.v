Require Import Games.Game.Player.
Require Import Games.Game.Game.

CoInductive strategy {G : Game} (p : Player) : GameState G -> Type :=
  | atom_strategy : forall b res,
      atomic_res b = Some res ->
      strategy p b
  | eloise_strategy : forall b,
      atomic_res b = None ->
      to_play b = p -> forall m,
      strategy p (exec_move b m) -> strategy p b
  | abelard_strategy : forall b,
      atomic_res b = None ->
      to_play b = opp p ->
      (forall m, strategy p (exec_move b m)) ->
      strategy p b.

Arguments atom_strategy {_} {_} {_} {_} _.
Arguments eloise_strategy {_} {_} {_} _ _ _.
Arguments abelard_strategy {_} {_} {_} _ _ _.

Definition strat_id {G} {p} {s : GameState G} (str : strategy p s) : strategy p s :=
  match str with
  | atom_strategy res_pf => atom_strategy res_pf
  | eloise_strategy res_pf play_pf m str => eloise_strategy res_pf play_pf m str
  | abelard_strategy res_pf play_pf strs => abelard_strategy res_pf play_pf strs
  end.

Lemma strat_id_eq {G : Game} {p} {s : GameState G} (str : strategy p s) :
  str = strat_id str.
Proof.
  destruct str; reflexivity.
Qed.

Inductive winning_strategy {G : Game} (p : Player) : forall {s : GameState G},
  strategy p s -> Prop :=
  | atom_strat_win : forall s (res_pf : atomic_res s = Some (Win p)),
      winning_strategy p (atom_strategy res_pf)
  | eloise_strat_win : forall s (res_pf : atomic_res s = None)
      (play_pf : to_play s = p) (m : Move s)
      (str : strategy p (exec_move s m)), winning_strategy p str ->
      winning_strategy p (eloise_strategy res_pf play_pf m str)
  | abelard_strat_win : forall s (res_pf : atomic_res s = None)
      (play_pf : to_play s = opp p)
      (strs : forall m, strategy p (exec_move s m)),
      (forall m, winning_strategy p (strs m)) ->
      winning_strategy p (abelard_strategy res_pf play_pf strs).

CoInductive no_worse_strategy {G : Game} (p : Player) : forall {s : GameState G},
  strategy p s -> Prop :=
  | atom_strat_draw_no_worse : forall s (res_pf : atomic_res s = Some Draw),
      no_worse_strategy p (atom_strategy res_pf)
  | atom_strat_win_no_worse : forall s (res_pf : atomic_res s = Some (Win p)),
      no_worse_strategy p (atom_strategy res_pf)
  | eloise_strat_no_worse : forall s (res_pf : atomic_res s = None)
      (play_pf : to_play s = p) (m : Move s)
      (str : strategy p (exec_move s m)), no_worse_strategy p str ->
      no_worse_strategy p (eloise_strategy res_pf play_pf m str)
  | abelard_strat_no_worse : forall s (res_pf : atomic_res s = None)
      (play_pf : to_play s = opp p)
      (strs : forall m, strategy p (exec_move s m)),
      (forall m, no_worse_strategy p (strs m)) ->
      no_worse_strategy p (abelard_strategy res_pf play_pf strs).

CoInductive drawing_strategy {G : Game} (p : Player) : forall {s : GameState G},
  strategy p s -> Prop :=
  | atom_strat_draw : forall s (res_pf : atomic_res s = Some Draw),
      drawing_strategy p (atom_strategy res_pf)
  | eloise_strat_draw : forall s (res_pf : atomic_res s = None)
      (play_pf : to_play s = p) (m : Move s)
      (str : strategy p (exec_move s m)), drawing_strategy p str ->
      drawing_strategy p (eloise_strategy res_pf play_pf m str)
  | abelard_strat_draw : forall s (res_pf : atomic_res s = None)
      (play_pf : to_play s = opp p)
      (strs : forall m, strategy p (exec_move s m)),
      (forall m, no_worse_strategy p (strs m)) ->
      drawing_strategy p (abelard_strategy res_pf play_pf strs).

CoInductive outcome : Type :=
  | W : Player -> outcome
  | step : outcome -> outcome.

CoFixpoint D : outcome := step D.

Definition outcome_id (o : outcome) : outcome :=
  match o with
  | W p => W p
  | step o => step o
  end.

Lemma outcome_id_eq (o : outcome) :
  o = outcome_id o.
Proof.
  destruct o; reflexivity.
Qed.

CoFixpoint play_game {G} {p} (s : GameState G) (str_pl : strategy p s) (str_opp : strategy (opp p) s) : outcome.
Proof.
  destruct str_pl.
  - destruct res.
    + exact (W p0).
    + exact D.
  - destruct str_opp.
    + congruence.
    + elim (opp_no_fp p); congruence.
    + apply step.
      exact (play_game G p _ str_pl (s m)).
  - destruct str_opp.
    + congruence.
    + apply step.
      exact (play_game G p _ (s m) str_opp).
    + elim (opp_no_fp (opp p)); congruence.
Defined.

CoInductive outcome_le : Player -> outcome -> outcome -> Prop :=
  | W_best : forall p o, outcome_le p o (W p)
  | W_worst : forall p o, outcome_le p (W (opp p)) o
  | step_mon : forall p o1 o2, outcome_le p o1 o2 -> outcome_le p (step o1) (step o2).

CoFixpoint outcome_le_refl : forall p o, outcome_le p o o.
Proof.
  intro p.
  destruct o.
  - destruct (player_id_or_opp_r_t p0 p); subst.
    + apply W_best.
    + apply W_worst.
  - apply step_mon.
    apply outcome_le_refl.
Qed.

Require Import Coq.Program.Equality.

CoFixpoint no_worse_strategy_correct {G} (p : Player) (b : GameState G)
  (s : strategy p b) (s' : strategy (opp p) b) : no_worse_strategy p s ->
  outcome_le p D (play_game b s s').
Proof.
  intro pf.
  rewrite outcome_id_eq.
  unfold outcome_id.
  unfold play_game.
  destruct s.
  - destruct res.
    + inversion pf; subst.
      apply W_best.
    + rewrite (outcome_id_eq D) at 1.
      unfold outcome_id.
      unfold D.
      apply step_mon.
      fold D.
      apply outcome_le_refl.
  - destruct s'.
    + congruence.
    + elim (opp_no_fp p).
      congruence.
    + fold @play_game.
      rewrite (outcome_id_eq D).
      unfold outcome_id.
      unfold D.
      apply step_mon.
      fold D.
      apply no_worse_strategy_correct.
      dependent destruction pf.
      auto.
  - destruct s'.
    + congruence.
    + fold @play_game.
      rewrite (outcome_id_eq D).
      unfold outcome_id.
      unfold D.
      apply step_mon.
      fold D.
      apply no_worse_strategy_correct.
      dependent destruction pf.
      apply H.
    + elim (opp_no_fp (opp p)); congruence.
Defined.

