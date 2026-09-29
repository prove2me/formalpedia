-- Prove2me | solution 1 for PrimeFractal.tendsto_intBoxCount_log_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:24:40.165783+00:00
-- url     : https://prove2.me/submissions/f65d5fb8-0c69-4971-a558-07ba0dacecd1

-- Sol generated from NumberTheory/PrimeFractalIntegers.lean
import Mathlib
import Definitions.Def_NumberTheory_PrimeFractalBoxDimension
import Definitions.Def_NumberTheory_PrimeFractalIntegers
import Theorems.Thm_PrimeFractal_boxIndex_le
import Theorems.Thm_PrimeFractal_eventually_intBoxCount_ge
import Theorems.Thm_PrimeFractal_eventually_two_le_log
import Theorems.Thm_PrimeFractal_tendsto_inv_log
import Theorems.Thm_PrimeFractal_tendsto_log_log_div_log

/-!
# The logarithmic lens cannot see primality

The same construction applied to *all* integers `≥ 2` produces the "integer
fractal" `{1 / log n : n ≥ 2}`.  We show it has

* Hausdorff dimension `0` (it is countable), and
* box-counting dimension `1` (`tendsto_intBoxCount_log_div`),

exactly like the prime fractal.  The proof of the lower bound is the same
separation estimate `boxIndex_lt`, but with no arithmetic input at all: for
integers one may simply count `Y - 1` of them below `Y`, where the primes needed
Chebyshev's theorem.

**Conclusion.** Both dimensions agree for the primes and for all integers, so
neither can detect primality: the mission's programme of reading off arithmetic
information (twin primes) from `dim (P, d)` is structurally impossible.  The
difference between the two sets is only visible in the second-order term (the
number of occupied boxes; see `NumberTheory.PrimeFractalRefined`).
-/

open PrimeFractal

open Filter Topology




theorem intBoxCount_le (m : ℕ) : intBoxCount m ≤ 2 * m + 1 := by
  have hsub : boxIndex m '' {n : ℕ | 2 ≤ n} ⊆ ↑(Finset.range (2 * m + 1)) := by
    rintro k ⟨p, hp, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (boxIndex_le m p hp)
  have h := Set.ncard_le_ncard hsub (Finset.range (2 * m + 1)).finite_toSet
  simpa [intBoxCount, Set.ncard_coe_finset] using h

theorem one_le_intBoxCount (m : ℕ) : 1 ≤ intBoxCount m := by
  have hfin : (boxIndex m '' {n : ℕ | 2 ≤ n}).Finite := by
    refine Set.Finite.subset (Finset.range (2 * m + 1)).finite_toSet ?_
    rintro k ⟨p, hp, rfl⟩
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.lt_succ_of_le (boxIndex_le m p hp)
  exact (Set.ncard_pos hfin).mpr ⟨boxIndex m 2, ⟨2, le_refl 2, rfl⟩⟩








open PrimeFractal in
theorem solution:
    Tendsto (fun m : ℕ => Real.log (intBoxCount m) / Real.log m) atTop (𝓝 1) := by
  have hupper : ∀ᶠ m : ℕ in atTop,
      Real.log (intBoxCount m) / Real.log m ≤ 1 + Real.log 3 * (1 / Real.log m) := by
    filter_upwards [eventually_two_le_log, eventually_ge_atTop 1] with m hL2 hm1
    have hL0 : 0 < Real.log m := by linarith
    have hm0 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hb : (intBoxCount m : ℝ) ≤ 3 * (m : ℝ) := by
      have h := intBoxCount_le m
      have h' : ((intBoxCount m : ℕ) : ℝ) ≤ ((2 * m + 1 : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      linarith
    have hb0 : (0 : ℝ) < (intBoxCount m : ℝ) := by
      have := one_le_intBoxCount m
      exact_mod_cast lt_of_lt_of_le zero_lt_one (by exact_mod_cast this)
    have hlog : Real.log (intBoxCount m) ≤ Real.log 3 + Real.log m := by
      have := Real.log_le_log hb0 hb
      rwa [Real.log_mul (by norm_num) (by linarith)] at this
    rw [div_le_iff₀ hL0]
    field_simp
    linarith
  have hlower : ∀ᶠ m : ℕ in atTop,
      1 - (Real.log 4 * (1 / Real.log m) + 3 * (Real.log (Real.log m) / Real.log m))
        ≤ Real.log (intBoxCount m) / Real.log m := by
    filter_upwards [eventually_intBoxCount_ge, eventually_two_le_log, eventually_ge_atTop 1]
      with m hge hL2 hm1
    have hL0 : 0 < Real.log m := by linarith
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hpos : (0 : ℝ) < (m : ℝ) / (4 * (Real.log m) ^ 3) := by positivity
    have hlog := Real.log_le_log hpos hge
    have hexp : Real.log ((m : ℝ) / (4 * (Real.log m) ^ 3))
        = Real.log m - Real.log 4 - 3 * Real.log (Real.log m) := by
      rw [Real.log_div (ne_of_gt hm0) (by positivity),
        Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    rw [hexp] at hlog
    rw [le_div_iff₀ hL0]
    field_simp
    linarith
  have h1 : Tendsto (fun m : ℕ => 1 + Real.log 3 * (1 / Real.log m)) atTop (𝓝 1) := by
    have := tendsto_inv_log.const_mul (Real.log 3)
    simpa using tendsto_const_nhds.add this
  have h2 : Tendsto (fun m : ℕ =>
      1 - (Real.log 4 * (1 / Real.log m) + 3 * (Real.log (Real.log m) / Real.log m)))
      atTop (𝓝 1) := by
    have ha := tendsto_inv_log.const_mul (Real.log 4)
    have hb := tendsto_log_log_div_log.const_mul (3 : ℝ)
    have := tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)) |>.sub (ha.add hb)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h2 h1 hlower hupper
