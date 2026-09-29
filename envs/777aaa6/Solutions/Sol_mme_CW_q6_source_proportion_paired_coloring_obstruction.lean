-- Prove2me | solution 1 for mme_CW_q6_source_proportion_paired_coloring_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T00:04:33.229553+00:00
-- url     : https://prove2.me/submissions/e0aa0bd0-3fbb-44ad-8fae-01ddfd943f2a

import Theorems.Thm_mme_CW_q6_paired_cyclic_coloring_balanced_fiber_bound
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MME BigOperators

/-- A weighted binomial expansion gives a uniform exponential bound at
the source proportion 1/19 without asymptotic estimates or Stirling's formula. -/
private theorem choose_nineteen_mul_le (m : ℕ) :
    (19 * m).choose m ≤ 64 ^ m := by
  have hterm : 18 ^ (18 * m) * (19 * m).choose m ≤ 19 ^ (19 * m) := by
    have hs := Finset.single_le_sum
      (f := fun i : ℕ => 1 ^ i * 18 ^ (19 * m - i) * (19 * m).choose i)
      (fun i _ => Nat.zero_le _) (show m ∈ Finset.range (19 * m + 1) by
        simp only [Finset.mem_range]; omega)
    have hsub : 19 * m - m = 18 * m := by omega
    dsimp only at hs
    have hsum := add_pow (1 : ℕ) 18 (19 * m)
    norm_cast at hsum
    rw [← hsum] at hs
    simpa [hsub] using hs
  have hbase : (19 : ℕ) ^ 19 ≤ 64 * 18 ^ 18 := by norm_num
  have hpow := Nat.pow_le_pow_left hbase m
  have hlarge : 19 ^ (19 * m) ≤ 18 ^ (18 * m) * 64 ^ m := by
    rw [mul_pow, ← pow_mul, ← pow_mul] at hpow
    simpa only [Nat.mul_comm] using hpow
  exact Nat.le_of_mul_le_mul_left (hterm.trans hlarge) (by positivity)

/-- At the exact rational source proportions, a primary middle-fiber mass
bound forces an exponential color count, modulo the supplied exponential loss. -/
theorem solution
    {m A H k : ℕ} (family : CWQ6PrimaryHashFamily (19 * m) m (18 * m) A H)
    (halving : family.CommonBalancedXYHalving) (hA : 0 < A)
    (coloring : (family.pairedCyclicConflictGraph halving).Coloring (Fin k))
    (loss : ℝ)
    (hmass : ((36 * m).choose (18 * m) : ℝ) * Real.exp (-loss) ≤
      4 * ((19 * m).choose (18 * m) : ℝ) ^ 2 * (H : ℝ)) :
    (2 : ℝ) ^ (5 * m) * Real.exp (-loss) ≤
      4 * (36 * (m : ℝ) + 1) * (k : ℝ) := by
  have hfiber : H ≤ k * 2 ^ (19 * m) :=
    (mme_CW_q6_paired_cyclic_coloring_balanced_fiber_bound
      family halving hA coloring).trans
      (Nat.mul_le_mul_left k (Nat.choose_le_two_pow _ _))
  have hchoose : ((19 * m).choose (18 * m) : ℝ) ≤ (2 : ℝ) ^ (6 * m) := by
    have hsym : (19 * m).choose (18 * m) = (19 * m).choose m := by
      simpa [show 19 * m - m = 18 * m by omega] using
        (Nat.choose_symm (n := 19 * m) (k := m) (by omega))
    have h := choose_nineteen_mul_le m
    rw [← hsym] at h
    have hp : (64 : ℝ) ^ m = (2 : ℝ) ^ (6 * m) := by rw [pow_mul]; norm_num
    rw [← hp]
    exact_mod_cast h
  have hmiddle : (2 : ℝ) ^ (36 * m) ≤
      (36 * (m : ℝ) + 1) * ((36 * m).choose (18 * m) : ℝ) := by
    have h := Nat.four_pow_le_two_mul_add_one_mul_central_binom (18 * m)
    have hn : 2 * (18 * m) = 36 * m := by omega
    rw [hn] at h
    have hp : (4 : ℝ) ^ (18 * m) = (2 : ℝ) ^ (36 * m) := by
      calc
        (4 : ℝ) ^ (18 * m) = ((2 : ℝ) ^ 2) ^ (18 * m) := by norm_num
        _ = _ := by rw [← pow_mul]; congr 1
    rw [← hp]
    exact_mod_cast h
  have hfiberR : (H : ℝ) ≤ (k : ℝ) * (2 : ℝ) ^ (19 * m) := by exact_mod_cast hfiber
  have hbound :
      (2 : ℝ) ^ (36 * m) * Real.exp (-loss) ≤
        (4 * (36 * (m : ℝ) + 1) * (k : ℝ)) * (2 : ℝ) ^ (31 * m) := by
    calc
      _ ≤ ((36 * (m : ℝ) + 1) * ((36 * m).choose (18 * m) : ℝ)) *
          Real.exp (-loss) := mul_le_mul_of_nonneg_right hmiddle (Real.exp_nonneg _)
      _ = (36 * (m : ℝ) + 1) *
          (((36 * m).choose (18 * m) : ℝ) * Real.exp (-loss)) := by ring
      _ ≤ (36 * (m : ℝ) + 1) *
          (4 * ((19 * m).choose (18 * m) : ℝ) ^ 2 * (H : ℝ)) := by gcongr
      _ ≤ (36 * (m : ℝ) + 1) *
          (4 * ((2 : ℝ) ^ (6 * m)) ^ 2 * ((k : ℝ) * 2 ^ (19 * m))) := by
        gcongr
      _ = _ := by
        have hexp : ((2 : ℝ) ^ (6 * m)) ^ 2 * 2 ^ (19 * m) = 2 ^ (31 * m) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          omega
        calc
          _ = (4 * (36 * (m : ℝ) + 1) * (k : ℝ)) *
              (((2 : ℝ) ^ (6 * m)) ^ 2 * 2 ^ (19 * m)) := by ring
          _ = _ := by rw [hexp]
  have hsplit : (2 : ℝ) ^ (36 * m) =
      (2 : ℝ) ^ (5 * m) * (2 : ℝ) ^ (31 * m) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit] at hbound
  have hpos : 0 < (2 : ℝ) ^ (31 * m) := by positivity
  apply (mul_le_mul_iff_right₀ hpos).mp
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbound
