-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_OrbitBlockArithmetic_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_OrbitBlockArithmetic_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:52:07.305924+00:00
-- url     : https://prove2.me/theorems/99e91e22-3ce2-44b4-871b-bdc52121df33
-- title:
--   Block arithmetic for double-exponential budgets
-- statement:
--   Contains source-proved natural-power and denominator-envelope inequalities that turn the canonical orbit growth estimates into explicit binary-tower index budgets. It introduces no additional analytic hypothesis.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR11/OrbitBlockArithmetic.lean#L1-L176
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR11_OrbitBlockArithmetic_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR11.OrbitBlockArithmetic.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_GlobalLcmHeight
import Definitions.Def_ErdosProblems_Erdos243_CumulativeLcmTransfer
import Definitions.Def_ErdosProblems_Erdos243_LcmCriticalBoundary
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PrimitiveRecordBarrier
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_RecordDivisibility_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_ProductDefect_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_LcmDefect_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_GrowthRecordEquivalence_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CanonicalGrowthBounds_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CoprimeCores_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_LogLogNormaliser_v243UnionFbf41fb8
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Orbit-supplied gcd and product budgets

Every gcd bound and every old-divisor
statement is derived from the exact two-coordinate orbit. In particular,
no pairwise-coprimality assumption is made on the original multipliers.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open PaperCompleteR7 Filter
open scoped BigOperators Topology

/-- Positive integer powers are monotone in the exponent. -/
theorem nat_pow_mono_exponent (a : ℕ) (ha : 1 ≤ a) {n m : ℕ}
    (hnm : n ≤ m) : a ^ n ≤ a ^ m :=
  Nat.pow_le_pow_right (by omega) hnm











/-- A natural-base double exponential is bounded by a shifted binary tower. -/
theorem natural_base_power_le_binaryTower (A n : ℕ) :
    A ^ (2 ^ n) ≤ binaryTower (n + A) := by
  have hA : A ≤ binaryTower A := by
    have h₁ := index_succ_le_two_pow A
    have h₂ := index_succ_le_two_pow (2 ^ A)
    unfold binaryTower
    omega
  calc
    A ^ (2 ^ n) ≤ binaryTower A ^ (2 ^ n) := Nat.pow_le_pow_left hA _
    _ = binaryTower (n + A) := by
      simp only [binaryTower, ← pow_mul, pow_add]
      congr 1
      ring

/-- A uniform multiplier majorant gives the denominator the same double
exponential order. The multiplicative initial denominator is retained. -/
theorem denominator_double_exponential_envelope
    (a D : ℕ → ℕ) (A : ℕ)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (ha : ∀ n, a n ≤ A ^ (2 ^ n)) :
    ∃ L : ℕ, ∀ n, D n ≤ binaryTower (n + L) := by
  let Q := max A (D 0)
  have hbound : ∀ n, D n ≤ Q ^ (2 ^ n) := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, pow_one] using (le_max_right A (D 0))
    | succ n ih =>
        rw [hD, doublePower_succ]
        have haQ : a n ≤ Q ^ (2 ^ n) :=
          (ha n).trans (Nat.pow_le_pow_left (le_max_left A (D 0)) _)
        have hh := Nat.mul_le_mul haQ ih
        simpa only [pow_two] using hh
  exact ⟨Q, fun n ↦ (hbound n).trans (natural_base_power_le_binaryTower Q n)⟩

/-- The canonical multiplier envelope is global; its finite prefix is not
silently discarded before a denominator product is formed. -/
theorem canonical_global_multiplier_envelope
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ n, a n ≤ A ^ (2 ^ n) := by
  obtain ⟨N, A, haN, hA, hb⟩ := quadratic_double_exponential_bounds a ha hapos hgrowth
  have hApos : 1 ≤ A := by omega
  refine ⟨A, hApos, fun n ↦ ?_⟩
  by_cases hn : N ≤ n
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hlow : a (N + k) ≤ A ^ (2 ^ k) := by have := (hb k).2; omega
    exact hlow.trans (nat_pow_mono_exponent A hApos (two_pow_mono (by omega)))
  · have hprefix : a n ≤ a N := ha.monotone (by omega)
    have hpow : A ≤ A ^ (2 ^ n) := by
      have h := nat_pow_mono_exponent A hApos
        (Nat.one_le_pow n 2 (by norm_num))
      simpa only [pow_one] using h
    exact hprefix.trans ((by omega : a N ≤ A).trans hpow)

/-- No denominator-growth hypothesis is added to the canonical endpoint. -/
theorem canonical_denominator_binaryTower_bound
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (q : ℕ)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    ∃ L : ℕ, ∀ n, canonicalDenominator a q n ≤ binaryTower (n + L) := by
  obtain ⟨A, hA, haA⟩ := canonical_global_multiplier_envelope a ha hapos hgrowth
  apply denominator_double_exponential_envelope a (canonicalDenominator a q) A
  · intro n
    simp only [canonicalDenominator, prefixProduct_succ]
    ring
  · exact haA

/-- The real geometric envelope is converted to an exact natural exponent
budget, including the finite prefix. -/
theorem runningMax_binary_exponent_of_real_envelope
    (U : ℕ → ℕ) (K : ℝ)
    (hK : ∀ n, (runningMax U n : ℝ) ≤ K * (2 : ℝ) ^ n) :
    ∃ L : ℕ, ∀ n, runningMax U n ≤ 2 ^ (L + n) := by
  obtain ⟨L, hL⟩ := exists_nat_gt K
  have hLpow : L ≤ 2 ^ L := by have := index_succ_le_two_pow L; omega
  refine ⟨L, fun n ↦ ?_⟩
  have hLreal : K ≤ (2 : ℝ) ^ L := by
    have hh : (L : ℝ) ≤ (2 : ℝ) ^ L := by exact_mod_cast hLpow
    exact hL.le.trans hh
  have h := (hK n).trans
    (mul_le_mul_of_nonneg_right hLreal (by positivity : (0 : ℝ) ≤ 2 ^ n))
  rw [← pow_add] at h
  exact_mod_cast h

/-- This integer envelope is supplied by the canonical reciprocal series. -/
theorem canonical_runningMax_binary_exponent
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    ∃ L : ℕ, ∀ n, runningMax (canonicalNaturalNumerator a p q) n ≤ 2 ^ (L + n) := by
  obtain ⟨K, hKpos, hC, hH⟩ :=
    canonical_runningMax_subexponential_envelope a ha hapos p q hq hs hgrowth 2 (by norm_num)
  exact runningMax_binary_exponent_of_real_envelope _ K hH

end ErdosProblems.Erdos243.PaperCompleteR11


