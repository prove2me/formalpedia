-- Prove2me | Theorems.Thm_Bridges_AttentionKneeGeometry_geometric_coarse_grid_overestimates
-- name    : Bridges.AttentionKneeGeometry.geometric_coarse_grid_overestimates
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:21:33.494858+00:00
-- url     : https://prove2.me/theorems/9cc123d7-57a4-41ef-a044-3b6f0cd0f46f
-- title:
--   A coarse grid genuinely overestimates.
-- statement:
--   **A coarse grid genuinely overestimates.**  On the power-of-two grid
--   `{2, 4, 8, 16}` the same profile reports a knee of `8`, a `33%` over-provision;
--   adding the single point `6` recovers the truth.  (Compare NET-63's coarse `28`
--   versus fine `24`.)
--
--   ```lean
--   theorem Bridges.AttentionKneeGeometry.geometric_coarse_grid_overestimates:
--       gridKnee {2, 4, 8, 16} geometricProfile 0.98 = 8 ∧
--         gridKnee {2, 4, 6, 8, 16} geometricProfile 0.98 = 6 ∧
--         knee geometricProfile 0.98 = 6 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AttentionKneeGeometry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AttentionKneeGeometry.lean#L411

-- Thm stub generated from Bridges/AttentionKneeGeometry.lean
import Mathlib
import Definitions.Def_Bridges_AttentionKneeGeometry
/-
  # The geometry of the retention knee: top-`k` attention mass, grids, and budgets

  ## Bridge: discrete convexity / majorization  ↔  limited-memory deployment tables

  This module gives a formal, assumption-explicit theory of the object that the
  NET-63 experiment series measures: the **retention knee**

      `k*(g) = least k such that the mass retained by the k largest keys is ≥ g`.

  The empirical thread (paper 148, round 16, "THE-2048-KNEE-IS-TWENTY-FOUR")
  reports, at context 2048 on corpus-A, gate `g = 0.98`, averaged over 12 windows:

      | k        | 20     | 24     | 28     | 32     |
      | retained | 0.9793 | 0.9835 | 0.9854 | 0.9885 |

  and the deployment chain `k* = 16, 20, 24` at contexts `512, 1024, 2048`,
  all inside a ~30-key budget.

  What we prove here (all statements are about an arbitrary nonnegative weight
  profile `w : ℕ → ℝ`, `mass w k = ∑_{i<k} w i`; when `w` is *antitone* this is
  exactly the top-`k` mass of a sorted attention row):

  * `knee` well-posedness: `knee_pass`, `knee_le_of_pass`, `mass_lt_of_lt_knee`,
    and the two-sided characterisation `pass_iff_knee_le`.
  * `knee_eq_of_fail_pass`: the "fail at `k-1`, pass at `k`" certificate that a
    sweep actually produces.
  * **Grid geometry.** A sweep only ever reports `gridKnee G`, the least *grid*
    point that passes.  We prove `knee_le_gridKnee` (a sweep never
    under-reports), `gridKnee_refine` (refining the grid can only *lower* the
    reported knee — the exact mechanism by which "28" became "24"), and
    `gridKnee_eq_knee_of_mem` (ON-grid landing).  `knee_bracket` turns the two
    numbers `0.9793 ✗ / 0.9835 ✓` into the sharp bracket `20 < k* ≤ 24`.
  * **Majorization ⇒ knee monotonicity.** If lengthening the context spreads the
    attention mass (`mass v k ≤ mass w k` for all `k`, i.e. `w` majorizes `v` in
    the partial-sum order) then `knee w g ≤ knee v g`, with a strict version
    `knee_lt_of_majorize_strict`.  This is the structural reason a chain like
    `16 < 20 < 24` is forced rather than coincidental (`deployment_chain`).
  * **Geometric tails ⇒ a finite key budget.** `knee_le_of_geometric_tail` and
    `exists_budget_of_geometric_tail`: an exponentially decaying attention tail
    always has a finite knee, with an explicit `C rᴺ ≤ 1 - g` certificate, and
    `knee_le_thirty_of_geometric_tail` is the "~30 keys" budget statement.
  * **An adversarial (Critic-stage) finding.** For antitone `w`, `mass` is
    *discretely concave*: equal-width block increments are antitone
    (`block_increment_antitone`), and averaging over windows preserves this
    (`avgMass_block_concave`).  The reported fine-grid row at 2048 **violates**
    this: `0.9854 - 0.9835 = 0.0019 < 0.0031 = 0.9885 - 0.9854`.  Hence
    `net63_fine2048_not_window_averaged_topk`: those four numbers cannot be the
    window-averaged top-`k` masses of any family of sorted attention rows.  The
    *knee* conclusion `k* = 24` survives (it only uses monotonicity), but the
    concavity-based extrapolation to `k = 28, 32` does not.

  * **Mixtures.**  `knee_mixture_le_max`: a convex blend of two heads never
    needs more keys than the harder of the two, so a multi-head budget is
    controlled by the worst head rather than by their sum.

  Everything is proved from scratch over `ℝ`; the concrete geometric example
  `geometricProfile` at the end exhibits a genuine coarse-grid overestimate
  (`geometric_coarse_grid_overestimates`: true knee 6, coarse grid reports 8).
-/


open Bridges.AttentionKneeGeometry

open Finset

/-! ## 1. Retained mass -/







/-! ## 2. The knee -/









/-! ## 3. Majorization: why the deployment chain is monotone -/



/-! ## 4. Grid geometry: what a sweep can and cannot report -/










/-! ## 5. Geometric tails and the key budget -/




/-! ## 6. Window averaging, and an obstruction -/



/-! ### The NET-63 round-16 fine grid at context 2048

Reported (12 windows, gate `g = 0.98`, corpus-A):
`R 20 = 0.9793`, `R 24 = 0.9835`, `R 28 = 0.9854`, `R 32 = 0.9885`.
-/






/-! ## 7. The deployment chain `16 < 20 < 24` -/



/-! ## 8. A concrete coarse-grid overestimate -/

theorem Bridges.AttentionKneeGeometry.geometric_coarse_grid_overestimates:
    gridKnee {2, 4, 8, 16} geometricProfile 0.98 = 8 ∧
      gridKnee {2, 4, 6, 8, 16} geometricProfile 0.98 = 6 ∧
      knee geometricProfile 0.98 = 6 := by sorry
