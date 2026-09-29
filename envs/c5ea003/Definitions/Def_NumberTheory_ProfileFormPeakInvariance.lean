-- Prove2me | Definitions.Def_NumberTheory_ProfileFormPeakInvariance
-- name    : NumberTheory_ProfileFormPeakInvariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:13:20.805229+00:00
-- url     : https://prove2.me/theorems/073b0fc4-7d2d-4d30-82b3-acfdf9f82961
-- title:
--   Aether Catalog definitions — NumberTheory_ProfileFormPeakInvariance
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.ProfileFormPeakInvariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/ProfileFormPeakInvariance.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormResidualPeak

/-!
# Profile form V: how robust is the interior peak?

Context (experiment 579, paper 229; V2 rule and the fragility gate).  The
beyond-Dickman residual was fitted by a concave quadratic pinned at the measured
end values `R(0) = 0.80`, `R(1) = 0.90`, with curvature coefficient `c` whose
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

namespace ProfileForm

open Set

/-- Endpoint-pinned concave fits of the beyond-Dickman residual: the quadratic
with `R(0) = 0.80`, `R(1) = 0.90` and curvature `c`. -/
noncomputable def residualQuad (c x : ℝ) : ℝ := 4/5 + (1/10 - c) * x + c * x ^ 2




/-- The vertex of the fit with curvature `c`. -/
noncomputable def residualQuadVertex (c : ℝ) : ℝ := (1/10 - c) / (-2 * c)











end ProfileForm


