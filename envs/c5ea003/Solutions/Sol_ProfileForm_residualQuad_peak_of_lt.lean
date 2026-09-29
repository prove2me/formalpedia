-- Prove2me | solution 1 for ProfileForm.residualQuad_peak_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:39:36.377988+00:00
-- url     : https://prove2.me/submissions/8c995e3a-7d88-4419-8c19-5a30a020aaa1

-- Sol generated from NumberTheory/ProfileFormPeakInvariance.lean
import Mathlib
import Definitions.Def_NumberTheory_ProfileFormPeakInvariance
import Definitions.Def_NumberTheory_ProfileFormResidualPeak
import Theorems.Thm_ProfileForm_exists_interiorMax_of_gt_endpoints
import Theorems.Thm_ProfileForm_not_antitoneOn_of_peak
import Theorems.Thm_ProfileForm_not_monotoneOn_of_peak

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






/-- Exact concavity identity around the vertex. -/
theorem residualQuad_vertex_identity {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    residualQuad c (residualQuadVertex c) - residualQuad c x
      = -c * (x - residualQuadVertex c) ^ 2 := by
  simp only [residualQuad, residualQuadVertex]
  field_simp
  ring


/-- **Threshold, peaked side.**  Curvature below `-1/10` puts the vertex strictly
inside the window (indeed in the right half). -/
theorem residualQuad_vertex_mem_Ioo {c : ℝ} (hc : c < -1/10) :
    residualQuadVertex c ∈ Ioo (1/2 : ℝ) 1 := by
  have hcneg : c < 0 := by linarith
  have hden : (0:ℝ) < -2 * c := by linarith
  constructor
  · rw [residualQuadVertex, lt_div_iff₀ hden]
    nlinarith
  · rw [residualQuadVertex, div_lt_one hden]
    nlinarith

/-- Strict global maximum at the vertex. -/
theorem residualQuad_lt_vertex {c x : ℝ} (hc : c < 0) (hx : x ≠ residualQuadVertex c) :
    residualQuad c x < residualQuad c (residualQuadVertex c) := by
  have hid := residualQuad_vertex_identity (ne_of_lt hc) x
  have hsq : 0 < (x - residualQuadVertex c) ^ 2 := by
    have : x - residualQuadVertex c ≠ 0 := sub_ne_zero.mpr hx
    positivity
  nlinarith








theorem solution{c : ℝ} (hc : c < -1/10) :
    (∃ m ∈ Ioo (0:ℝ) 1, IsMaxOn (residualQuad c) (Icc (0:ℝ) 1) m) ∧
      ¬ MonotoneOn (residualQuad c) (Icc (0:ℝ) 1) ∧
      ¬ AntitoneOn (residualQuad c) (Icc (0:ℝ) 1) := by
  have hcneg : c < 0 := by linarith
  have hv := residualQuad_vertex_mem_Ioo hc
  have hvIoo : residualQuadVertex c ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hv.1], hv.2⟩
  have h0 : residualQuad c 0 < residualQuad c (residualQuadVertex c) :=
    residualQuad_lt_vertex hcneg (by intro h; rw [← h] at hv; linarith [hv.1])
  have h1 : residualQuad c 1 < residualQuad c (residualQuadVertex c) :=
    residualQuad_lt_vertex hcneg (by intro h; rw [h] at hv; linarith [hv.2])
  have hcont : ContinuousOn (residualQuad c) (Icc (0:ℝ) 1) := by
    apply Continuous.continuousOn
    unfold residualQuad
    fun_prop
  exact ⟨exists_interiorMax_of_gt_endpoints hcont hvIoo h0 h1,
    not_monotoneOn_of_peak hvIoo h1, not_antitoneOn_of_peak hvIoo h0⟩
