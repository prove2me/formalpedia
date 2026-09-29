-- Prove2me | solution 1 for Logic.StateHorizon.exists_state_horizon
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:09:31.667149+00:00
-- url     : https://prove2.me/submissions/7bc8e78f-f734-443c-85f7-ac3e57c2d35d

-- Sol generated from Logic/DenseFinalStepStateHorizon.lean
import Mathlib
import Definitions.Def_Logic_DenseFinalStepStateHorizon
import Theorems.Thm_Logic_StateHorizon_readout_gap_lt
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
theorem solution(A : E →L[ℝ] E) (u : E) (r : E →L[ℝ] ℝ)
    {lam R Delta gamma : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (hA : ∀ z : E, ‖A z‖ ≤ lam * ‖z‖) (hr : ∀ z : E, ‖r z‖ ≤ R * ‖z‖) (hR : 0 ≤ R)
    (hDelta : 0 ≤ Delta) (hgamma : 0 < gamma) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x y : E, ‖x - y‖ ≤ Delta →
      |r ((step A u)^[n] x) - r ((step A u)^[n] y)| < gamma := by
  rcases eq_or_lt_of_le hlam with hzero | hpos
  · -- `lam = 0`: the state collapses after one step
    refine ⟨1, fun n hn x y hxy => ?_⟩
    have hpow : lam ^ n = 0 := by
      rw [← hzero]
      exact zero_pow (by omega)
    refine readout_gap_lt A u r hlam hA hr hR x y hxy n ?_
    rw [hpow]
    simpa using hgamma
  · have hDR : 0 ≤ Delta * R := mul_nonneg hDelta hR
    rcases eq_or_lt_of_le hDR with hDR0 | hDRpos
    · refine ⟨0, fun n _ x y hxy => ?_⟩
      refine readout_gap_lt A u r hlam hA hr hR x y hxy n ?_
      rw [← hDR0, mul_zero]
      exact hgamma
    · obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hgamma hDRpos) hlam1
      refine ⟨N, fun n hn x y hxy => ?_⟩
      have hmono : lam ^ n ≤ lam ^ N := pow_le_pow_of_le_one hlam hlam1.le hn
      have hlt : lam ^ n < gamma / (Delta * R) := lt_of_le_of_lt hmono hN
      refine readout_gap_lt A u r hlam hA hr hR x y hxy n ?_
      rw [← lt_div_iff₀ hDRpos]
      exact hlt
