Require Import Lia.
Require Import List.

Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Strategy.

Inductive win {G : Game} (p : Player) : GameState G -> Type :=
  | atom_win : forall b,
      atomic_res b = Some (Win p) ->
      win p b
  | eloise_win : forall b,
      atomic_res b = None ->
      to_play b = p ->
      forall m, win p (exec_move b m) ->
      win p b
  | abelard_win : forall b,
      atomic_res b = None ->
      to_play b = opp p ->
      (forall m, win p (exec_move b m)) ->
      win p b.

Arguments atom_win {_} {_} {_} _.
Arguments eloise_win {_} {_} {_} _ _ _ _.
Arguments abelard_win {_} {_} {_} _ _ _.

Fixpoint depth {G} {p} {s : GameState G} (w : win p s) : nat :=
  match w with
  | atom_win _ => 0
  | eloise_win _ _ _ w' => S (depth w')
  | @abelard_win _ _ s _ _ ws => S (list_max
      (map (fun m => depth (ws m)) (enum_moves s)))
  end.


Definition minimal {G} {p} {s : GameState G} (w : win p s) : Prop :=
  forall (w' : win p s), depth w <= depth w'.

Definition mate {G} (p : Player) (s : GameState G) (n : nat) : Type :=
  { w : win p s & depth w = n /\ minimal w }.

Fixpoint strategy_of_win {G : Game} {p : Player} {s : GameState G}
  (w : win p s) : strategy p s :=
  match w with
  | atom_win res_pf =>
      atom_strategy res_pf
  | eloise_win res_pf play_pf m w =>
      eloise_strategy res_pf play_pf m (strategy_of_win w)
  | abelard_win res_pf play_pf ws =>
      abelard_strategy res_pf play_pf (fun m =>
        strategy_of_win (ws m))
  end.

Lemma strategy_of_win_correct {G : Game} {p : Player} (s : GameState G)
  (w : win p s) : winning_strategy p (strategy_of_win w).
Proof.
  induction w; constructor; auto.
Qed.

Lemma unique_winner {G} : forall p p' (b : GameState G),
  win p b -> win p' b -> p = p'.
Proof.
  intros p p' b w; induction w; intro w'.
  - destruct w'; congruence.
  - destruct w'; try congruence; auto.
  - destruct w'; try congruence.
    + apply (H m); exact w'.
    + apply opp_inj; congruence.
Qed.
