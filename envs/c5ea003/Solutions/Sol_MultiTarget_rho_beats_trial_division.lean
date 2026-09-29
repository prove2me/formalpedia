-- Prove2me | solution 1 for MultiTarget.rho_beats_trial_division
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:14:22.001919+00:00
-- url     : https://prove2.me/submissions/da620714-fd42-44af-8242-13f545b5d763

-- Sol generated from Bridges/MultiTargetTrialDivision.lean
import Mathlib
import Definitions.Def_Bridges_MultiTargetTrialDivision
import Definitions.Def_Bridges_TreeSieveLottery

/-!
# The multi-target relaxation is exactly trial division

This file formalises the analysis of the "MULTI-TARGET" relaxation
(round-72 experiment `exp558`).  A tree search whose goal is the *exact* target
`a = N` is relaxed to the much weaker goal `gcd (a, N) > 1`.  Empirically the
relaxation is a `~10^12` speedup over blind FIFO search, but `100 %` of first
hits land at `a = min (p, q)`, with fitted exponent `α = 1.087`, `r² = 1.0`:
dead centre of the trial-division band.  The theorems below explain *why* this
is forced, not accidental.

Main results.

* `firstHit_eq_min` / `isLeast_hit_min` — the least `a ≥ 2` with `gcd (a, N) > 1`
  is **exactly** `min p q` for a semiprime `N = p * q`.  Any search that sweeps
  values in ascending order therefore always first hits at `min p q`; the
  observed histogram is a theorem, not a statistic.
* `min_sq_le` / `ascending_sweep_is_trial_division` — the cost of the ascending
  sweep is `min p q ≤ √N`: exactly the trial-division exponent `1/2`.
* `relaxation_speedup_exact` — relative to the exact target `a = N`, the
  relaxation saves precisely a factor `max p q`, which is between `√N` and
  `N / 2`: a huge but strictly bounded win.
* `rho_beats_trial_division` — the `N^{1/4}` cost of Pollard-ρ beats
  `C · N^{1/2}`-class trial division for every constant `C` once `N > C⁴`;
  so the relaxed search remains dominated.
* `tree_integer_face_trichotomy` — the capstone: any splitter reading a value
  off the integer face of the Berggren tree is in one of three regimes —
  integer square identity (returns `N`, no split), a genuine mod-`N` congruence
  of squares (Dixon/QS class), or an ascending value sweep (trial division,
  cost `min p q`).  Every route ends in a known method.
-/

open MultiTarget

open TreeSieve

/-! ## The ascending sweep first-hit theorem -/







/-! ## The cost of the sweep is the trial-division exponent -/






/-! ## Pollard-ρ still dominates -/


/-! ## Capstone: every route through the integer face is a known method -/






open MultiTarget in
theorem solution{C N : ℝ} (hC : 0 < C) (hN : C ^ 4 < N) :
    C * N ^ ((1:ℝ)/4) < N ^ ((1:ℝ)/2) := by
  have hNpos : (0:ℝ) < N := lt_of_le_of_lt (by positivity) hN
  have h4 : (0:ℝ) < N ^ ((1:ℝ)/4) := Real.rpow_pos_of_pos hNpos _
  have hCN : C < N ^ ((1:ℝ)/4) := by
    have hCC : C = (C ^ 4) ^ ((1:ℝ)/4) := by
      rw [← Real.rpow_natCast C 4, ← Real.rpow_mul hC.le]
      norm_num
    calc C = (C ^ 4) ^ ((1:ℝ)/4) := hCC
      _ < N ^ ((1:ℝ)/4) := by
          apply Real.rpow_lt_rpow (by positivity) hN (by norm_num)
  calc C * N ^ ((1:ℝ)/4) < N ^ ((1:ℝ)/4) * N ^ ((1:ℝ)/4) :=
        mul_lt_mul_of_pos_right hCN h4
    _ = N ^ ((1:ℝ)/2) := by
        rw [← Real.rpow_add hNpos]; norm_num
