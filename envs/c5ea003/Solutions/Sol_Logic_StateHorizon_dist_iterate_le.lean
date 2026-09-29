-- Prove2me | solution 1 for Logic.StateHorizon.dist_iterate_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:03:38.696958+00:00
-- url     : https://prove2.me/submissions/aa7c4fde-54d7-4424-9f5a-f896081b5a21

-- Sol generated from Logic/DenseFinalStepStateHorizon.lean
import Mathlib
import Definitions.Def_Logic_DenseFinalStepStateHorizon
/-
# NET-25 / Catalog·Logic — The state horizon of a contractive carry cell, and how
# much depth a rich boundary step buys

Third component of the NET-25 dissection.  The empirical round measured a
*state horizon*: a raw-input GRU carry cell masters `n = 5` and then decays with
depth (`raw20-192`, 7 seeds: `0.0806, 0.6997, 0.0103, 0.0063, 0.0093, 0.0020,
0.0132` at `n = 8`), while the carry *transition* probe stays at `0.86–0.99`
throughout.  The failure is therefore a **readout separation** failure.

This file proves the corresponding mathematical statement and its quantitative
cure.

* `Logic.StateHorizon.dist_iterate_le` — a contractive affine recurrence
  (`‖A x‖ ≤ lam ‖x‖`, `lam < 1`) squeezes the separation of two trajectories
  geometrically: `‖f^[n] x - f^[n] y‖ ≤ lam ^ n * ‖x - y‖`.
* `Logic.StateHorizon.readout_gap_lt` and `exists_state_horizon` — hence **any**
  bounded linear readout loses any fixed decision margin `gamma` beyond a finite
  depth `N`: the state horizon is a theorem, not an artifact.  This is a genuine
  impossibility statement (no training procedure and no parameter count can
  avoid it, only a *less contractive* cell or a *boundary gain* can).
* `Logic.StateHorizon.horizon_shift` and `horizon_shift_log` — a final-step gain
  `m ≥ 1` (the formal stand-in for a dense EOS input pathway) extends the usable
  depth by exactly `k ≈ log m / log (1 / lam)` steps: **boundary richness buys
  depth only logarithmically**.

That last item is the sharp, falsifiable prediction of this round: the usable
unroll depth of a state-augmented answer path should grow like the *logarithm*
of the boundary gain, so the observed `20/28 fail, 384 works` gap corresponds to
a modest additive depth gain, not to a qualitative change of regime.

Companion files: `Logic.DenseFinalStepCarryChain` (the transition is exactly
length-general), `Logic.DenseFinalStepBoundaryConditioning` (EOS width is
invisible to the function class, visible to the optimiser).
-/


open Logic.StateHorizon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


theorem step_sub (A : E →L[ℝ] E) (u x y : E) :
    step A u x - step A u y = A (x - y) := by
  simp [step, map_sub]






/-! ## Lab notes (round-net-25, measured)

`raw20-192` (125,214 params, 20-d EOS), 7 seeds at `n = 8` full:
`0.0806, 0.6997, 0.0103, 0.0063, 0.0093, 0.0020, 0.0132` — a *distribution*
rather than a hard wall, with the final-carry probe at `0.86–0.99` in every one
of them.  `exists_state_horizon` explains the shape: with a contractive cell the
readout margin is lost at a finite depth that depends on `lam`, `Delta`, `R`,
`gamma`, all of which vary with the seed — hence a spread of horizons rather
than a single threshold.  `horizon_shift_log` predicts that the cure's depth
benefit is logarithmic in the boundary gain, so the untested `28 → 384` window
should show a smooth, log-spaced improvement rather than a sharp threshold.
-/


open Logic.StateHorizon in
theorem solution(A : E →L[ℝ] E) (u : E) {lam : ℝ} (hlam : 0 ≤ lam)
    (hA : ∀ z : E, ‖A z‖ ≤ lam * ‖z‖) (x y : E) (n : ℕ) :
    ‖(step A u)^[n] x - (step A u)^[n] y‖ ≤ lam ^ n * ‖x - y‖ := by
  induction n generalizing x y with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      refine (ih (step A u x) (step A u y)).trans ?_
      have h1 : ‖step A u x - step A u y‖ ≤ lam * ‖x - y‖ := by
        rw [step_sub]; exact hA _
      have hpow : (0 : ℝ) ≤ lam ^ n := pow_nonneg hlam n
      calc lam ^ n * ‖step A u x - step A u y‖ ≤ lam ^ n * (lam * ‖x - y‖) :=
            mul_le_mul_of_nonneg_left h1 hpow
        _ = lam ^ (n + 1) * ‖x - y‖ := by ring
