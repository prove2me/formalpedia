-- Prove2me | Theorems.Thm_ProfileForm_residualQuad_peak_of_lt
-- name    : ProfileForm.residualQuad_peak_of_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:37:55.704016+00:00
-- url     : https://prove2.me/theorems/1cac05d0-ee35-443b-ac8d-ba5f6483184a
-- title:
--   Peakedness on the whole sub-threshold range.
-- statement:
--   **Peakedness on the whole sub-threshold range.**
--
--   ```lean
--   theorem ProfileForm.residualQuad_peak_of_lt{c : ℝ} (hc : c < -1/10) :
--       (∃ m ∈ Ioo (0:ℝ) 1, IsMaxOn (residualQuad c) (Icc (0:ℝ) 1) m) ∧
--         ¬ MonotoneOn (residualQuad c) (Icc (0:ℝ) 1) ∧
--         ¬ AntitoneOn (residualQuad c) (Icc (0:ℝ) 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ProfileFormPeakInvariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ProfileFormPeakInvariance.lean#L120

-- Thm stub generated from NumberTheory/ProfileFormPeakInvariance.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormPeakInvariance
import Definitions.Def_NumberTheory_ProfileFormResidualPeak

/-!
# Profile form V: how robust is the interior peak?

Context (experiment 579, paper 229; V2 rule and the fragility gate).  The
beyond-Dickman residual was fitted by a concave quadratic pinned at the measured
confidence interval is `[-0.62, -0.14]`; the reported vertex is `0.59`, interior,
and the verdict "PEAKED" was declared invariant across all three offset-`r`
brackets.

This file replaces the single fit by the whole one-parameter family

`residualQuad c x = 4/5 + (1/10 - c) x + c x²`  (the endpoint-pinned fits),

and asks which curvatures actually produce an interior peak.  The answer is a
sharp threshold at `c = -1/10`:

* `residualQuad_vertex_mem_Ioo` — for `c < -1/10` the vertex lies in `(1/2, 1)`;
* `residualQuad_peak_of_lt` — and the fit is then genuinely peaked: strict
  interior maximum, neither monotone nor antitone on the window;
* `residualQuad_monotoneOn_of_ge` — for `-1/10 ≤ c < 0` the fit is *monotone*
  on the window: no peak at all;
* `residualQuad_peak_invariant_over_CI` — the whole measured interval
  `[-0.62, -0.14]` sits on the peaked side, so the verdict is invariant across
  the reported bootstrap range, with margin `0.04` to the threshold;
* `residualQuad_hump_ratio_ge` — the apex of every concave endpoint-pinned fit
  overshoots the wall end value by at least `12 %` (the apex is attained inside
  the window exactly when `c < -1/10`), and
* `residualQuad_peak_gt_right_end` — the apex always overshoots the far end
  value too;
* `residualQuad_eq_residualFit` — the reported fit is the member `c = -5/9`.
-/

open ProfileForm

open Set

theorem ProfileForm.residualQuad_peak_of_lt{c : ℝ} (hc : c < -1/10) :
    (∃ m ∈ Ioo (0:ℝ) 1, IsMaxOn (residualQuad c) (Icc (0:ℝ) 1) m) ∧
      ¬ MonotoneOn (residualQuad c) (Icc (0:ℝ) 1) ∧
      ¬ AntitoneOn (residualQuad c) (Icc (0:ℝ) 1) := by sorry
