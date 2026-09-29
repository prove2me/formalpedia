-- Prove2me | Theorems.Thm_Logic_StateHorizon_dist_iterate_le
-- name    : Logic.StateHorizon.dist_iterate_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:34:45.100999+00:00
-- url     : https://prove2.me/theorems/d8913226-8c00-4ec6-a81d-80f57e0cbd6a
-- title:
--   Geometric collapse of state separation.
-- statement:
--   **Geometric collapse of state separation.**  Under a contraction factor
--   `lam`, two trajectories of the same cell approach each other geometrically.
--
--   ```lean
--   theorem Logic.StateHorizon.dist_iterate_le(A : E →L[ℝ] E) (u : E) {lam : ℝ} (hlam : 0 ≤ lam)
--       (hA : ∀ z : E, ‖A z‖ ≤ lam * ‖z‖) (x y : E) (n : ℕ) :
--       ‖(step A u)^[n] x - (step A u)^[n] y‖ ≤ lam ^ n * ‖x - y‖ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/DenseFinalStepStateHorizon.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/DenseFinalStepStateHorizon.lean#L49

-- Thm stub generated from Logic/DenseFinalStepStateHorizon.lean
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

theorem Logic.StateHorizon.dist_iterate_le(A : E →L[ℝ] E) (u : E) {lam : ℝ} (hlam : 0 ≤ lam)
    (hA : ∀ z : E, ‖A z‖ ≤ lam * ‖z‖) (x y : E) (n : ℕ) :
    ‖(step A u)^[n] x - (step A u)^[n] y‖ ≤ lam ^ n * ‖x - y‖ := by sorry
