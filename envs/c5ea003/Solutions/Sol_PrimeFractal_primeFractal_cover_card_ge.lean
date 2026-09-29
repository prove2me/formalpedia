-- Prove2me | solution 1 for PrimeFractal.primeFractal_cover_card_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T01:26:27.670997+00:00
-- url     : https://prove2.me/submissions/d5d84e51-f3b7-4558-9296-196d7a9f45fa

-- Sol generated from NumberTheory/PrimeFractalCovering.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalHausdorff
import Definitions.Def_NumberTheory_PrimeFractalRefined
import Theorems.Thm_PrimeFractal_boxCountSet_le_two_mul_cover
import Theorems.Thm_PrimeFractal_boxCount_eq_boxCountSet
import Theorems.Thm_PrimeFractal_eventually_boxCount_ge
import Theorems.Thm_PrimeFractal_eventually_two_le_log
import Theorems.Thm_PrimeFractal_one_le_boxCount
import Theorems.Thm_PrimeFractal_tendsto_inv_log
import Theorems.Thm_PrimeFractal_tendsto_log_log_div_log

/-!
# Robustness of the box dimension: grid boxes versus arbitrary covers

`NumberTheory.PrimeFractalBoxDimension` computes the box dimension of the prime
fractal with *grid* boxes `[k/m, (k+1)/m)`.  A critic may object that the value
of a "dimension" must not depend on that choice.  It does not: an interval of
length `1/m` meets at most two grid boxes, so any cover of `S` by `K` intervals
of length `1/m` satisfies `boxCountSet S m ≤ 2 K`.

Consequently the dimension-`1` lower bound survives verbatim for the
covering-number definition of the Minkowski dimension
(`primeFractal_cover_card_ge`): however cleverly one covers the primes by
intervals of length `1/m`, one needs `m^{1-o(1)}` of them.
-/

open PrimeFractal

open Filter Topology




open PrimeFractal in
theorem solution{ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ I : Set ℝ, I.Finite →
      primeFractal ⊆ (⋃ c ∈ I, Set.Icc c (c + 1 / (m : ℝ))) →
      1 - ε ≤ Real.log I.ncard / Real.log m := by
  have hsmall : Tendsto (fun m : ℕ =>
      (Real.log 32) * (1 / Real.log m) + 4 * (Real.log (Real.log m) / Real.log m))
      atTop (𝓝 0) := by
    have ha := tendsto_inv_log.const_mul (Real.log 32)
    have hb := tendsto_log_log_div_log.const_mul (4 : ℝ)
    simpa using ha.add hb
  filter_upwards [eventually_boxCount_ge, eventually_two_le_log, eventually_ge_atTop 1,
    hsmall.eventually (gt_mem_nhds hε)] with m hge hL2 hm1 hsm
  intro I hIfin hcov
  have hL0 : 0 < Real.log m := by linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  -- transfer the grid lower bound to the cover
  have hbox : boxCount m ≤ 2 * I.ncard := by
    rw [boxCount_eq_boxCountSet]
    exact boxCountSet_le_two_mul_cover hIfin hcov
  have hbox' : (boxCount m : ℝ) ≤ 2 * (I.ncard : ℝ) := by exact_mod_cast hbox
  have hbc1 : (1 : ℝ) ≤ (boxCount m : ℝ) := by exact_mod_cast one_le_boxCount m
  have hIpos : (0 : ℝ) < (I.ncard : ℝ) := by linarith
  -- lower bound for `log (boxCount m)`
  have hpos : (0 : ℝ) < (m : ℝ) / (16 * (Real.log m) ^ 4) := by positivity
  have hlog := Real.log_le_log hpos hge
  have hexp : Real.log ((m : ℝ) / (16 * (Real.log m) ^ 4))
      = Real.log m - Real.log 16 - 4 * Real.log (Real.log m) := by
    rw [Real.log_div (ne_of_gt hm0) (by positivity),
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  rw [hexp] at hlog
  have hlogI : Real.log (boxCount m) ≤ Real.log 2 + Real.log I.ncard := by
    have h := Real.log_le_log (by linarith) hbox'
    rwa [Real.log_mul (by norm_num) (ne_of_gt hIpos)] at h
  have hlog32 : Real.log 32 = Real.log 16 + Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  have hkey : Real.log m - Real.log 32 - 4 * Real.log (Real.log m) ≤ Real.log I.ncard := by
    rw [hlog32]
    linarith [hlog, hlogI]
  rw [le_div_iff₀ hL0]
  have hsm' : Real.log 32 * (1 / Real.log m) + 4 * (Real.log (Real.log m) / Real.log m) < ε :=
    hsm
  have hmul : Real.log 32 + 4 * Real.log (Real.log m) < ε * Real.log m := by
    have h1 : Real.log 32 * (1 / Real.log m) = Real.log 32 / Real.log m := by ring
    have h2 : (Real.log 32 + 4 * Real.log (Real.log m)) / Real.log m < ε := by
      rw [add_div]
      rw [h1] at hsm'
      have : 4 * (Real.log (Real.log m) / Real.log m)
          = 4 * Real.log (Real.log m) / Real.log m := by ring
      linarith [hsm', this.le, this.ge]
    rw [div_lt_iff₀ hL0] at h2
    linarith
  linarith [hkey, hmul]
