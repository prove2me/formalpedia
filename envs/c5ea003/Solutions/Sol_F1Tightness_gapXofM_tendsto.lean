-- Prove2me | solution 1 for F1Tightness.gapXofM_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:58:03.494093+00:00
-- url     : https://prove2.me/submissions/b143f1f0-b618-493e-b7eb-e85297ef605f

-- Sol generated from Probability/F1TightnessDiscretisation.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Definitions.Def_Probability_F1TightnessDiscretisation

/-!
# Discretisation bias of the slack factor (paper 250, next-cycle item)

The measured slack factor is computed on a finite cell grid (27 cells), while
the profile it summarises is a continuum density.  The exact identity
`gapX p = (M+1)/(2·M·E_x + 1)` of `Probability.F1TightnessCore` isolates the
grid dependence in a single scalar function, and this file settles its
behaviour: at a fixed mean probe position `E < 1/2` the finite-grid slack is
**strictly below** the continuum value `1/(2E)`, increases with the number of
cells, and converges to it.  Consequently a finite-grid estimate of the F1
slack is conservative.

Main results.

* `gapXofM` — the grid-dependent slack `X_M(E) = (M+1)/(2ME+1)`.
* `gapX_eq_gapXofM` — it is the slack of any profile with mean position `E`.
* `gapXofM_lt_continuum` — `X_M(E) < 1/(2E)` for every `M`, when `E < 1/2`.
* `gapXofM_strictMono` — `X_M(E)` strictly increases in the number of cells.
* `gapXofM_tendsto` — `X_M(E) → 1/(2E)`.
* `finite_grid_underestimates` — the packaged statement: the reported slack is
  a strict lower bound for the continuum slack of the same profile.
-/

open Filter

open F1Tightness









open F1Tightness in
theorem solution{E : ℝ} (hE0 : 0 < E) :
    Tendsto (gapXofM E) atTop (nhds (1 / (2 * E))) := by
  have hinv : Tendsto (fun M : ℕ => 1 / (M : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum : Tendsto (fun M : ℕ => 1 + 1 / (M : ℝ)) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).add hinv
  have hden : Tendsto (fun M : ℕ => 2 * E + 1 / (M : ℝ)) atTop (nhds (2 * E)) := by
    simpa using (tendsto_const_nhds (x := 2 * E) (f := atTop (α := ℕ))).add hinv
  have hne : (2 : ℝ) * E ≠ 0 := by positivity
  have hdiv := hnum.div hden hne
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with M hM
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  show (1 + 1 / (M : ℝ)) / (2 * E + 1 / (M : ℝ)) = gapXofM E M
  unfold gapXofM
  rw [div_eq_div_iff (by positivity) (by positivity)]
  field_simp
