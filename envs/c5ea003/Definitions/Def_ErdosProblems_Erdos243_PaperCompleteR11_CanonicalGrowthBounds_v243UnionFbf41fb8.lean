-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CanonicalGrowthBounds_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_CanonicalGrowthBounds_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:49:42.03349+00:00
-- url     : https://prove2.me/theorems/73bf172e-e3d5-4fbb-aba9-6eb9bc5fc04e
-- title:
--   Explicit canonical growth bounds
-- statement:
--   Contains proved power-tower, monotonicity, quadratic-bracket, and canonical numerator envelope estimates. These are quantitative input lemmas for the record argument, not a claim that the unrestricted Erdős problem is solved.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR11/CanonicalGrowthBounds.lean#L1-L191
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR11_CanonicalGrowthBounds_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR11.CanonicalGrowthBounds.

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
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Fin.Pigeonhole
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
# Quantitative growth suppliers for the inclusive record argument


The original reciprocal sequence supplies explicit double-exponential
bounds.  The canonical numerator and its *running maximum* have an
arbitrarily slow geometric envelope.  None of these bounds is inserted
as an extra premise in the canonical corollaries.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open Filter PaperCompleteR7
open scoped Topology

/-- The natural double-power identity used without taking logarithms. -/
theorem doublePower_succ (b k : ℕ) : b ^ (2 ^ (k + 1)) = (b ^ (2 ^ k)) ^ 2 := by
  rw [pow_succ (2 : ℕ) k, pow_mul]

/-- Strict increase gives the elementary linear lower bound, including a₀=1. -/
theorem strictMono_nat_linear_lower (a : ℕ → ℕ) (ha : StrictMono a) :
    ∀ n, a 0 + n ≤ a n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hh := ha (Nat.lt_succ_self n)
      have hh' : a n + 1 ≤ a (n + 1) := by
        simpa [Nat.succ_eq_add_one] using hh
      omega

/-- Fixed rational quadratic brackets are derived from the actual limit. -/
theorem quadratic_brackets_of_limit
    (a : ℕ → ℕ) (hapos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    ∃ N : ℕ, ∀ n, N ≤ n →
      a n ^ 2 ≤ 2 * a (n + 1) ∧ a (n + 1) ≤ 2 * a n ^ 2 := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hgrowth (1 / 2) (by norm_num)
  refine ⟨N, fun n hn ↦ ?_⟩
  have hh := hN n hn
  rw [Real.dist_eq] at hh
  have hl : (1 / 2 : ℝ) ≤ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2 := by
    have hh' := (abs_lt.mp hh).1
    linarith
  have hu : (a (n + 1) : ℝ) / (a n : ℝ) ^ 2 ≤ 2 := by
    have hh' := (abs_lt.mp hh).2
    linarith
  have hsq : (0 : ℝ) < (a n : ℝ) ^ 2 := by
    have hp : (0 : ℝ) < (a n : ℝ) := by exact_mod_cast hapos n
    positivity
  have hl' := (le_div_iff₀ hsq).1 hl
  have hu' := (div_le_iff₀ hsq).1 hu
  constructor
  · have hh' : (a n : ℝ) ^ 2 ≤ 2 * (a (n + 1) : ℝ) := by linarith
    exact_mod_cast hh'
  · exact_mod_cast hu'

/-- Explicit double-exponential growth on one common tail.  The same N
works simultaneously for every later index, so growing blocks are allowed. -/
theorem quadratic_double_exponential_bounds
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    ∃ N A : ℕ, 4 ≤ a N ∧ A = 2 * a N ∧ ∀ k : ℕ,
      2 * 2 ^ (2 ^ k) ≤ a (N + k) ∧ 2 * a (N + k) ≤ A ^ (2 ^ k) := by
  obtain ⟨N₀, hN₀⟩ := quadratic_brackets_of_limit a hapos hgrowth
  let N := max N₀ 3
  have hN : N₀ ≤ N := le_max_left _ _
  have haN : 4 ≤ a N := by
    have hh := strictMono_nat_linear_lower a ha N
    have hp := hapos 0
    have h3 : 3 ≤ N := le_max_right _ _
    omega
  refine ⟨N, 2 * a N, haN, rfl, ?_⟩
  intro k
  induction k with
  | zero => simpa using And.intro haN (le_refl (2 * a N))
  | succ k ih =>
      have hq := hN₀ (N + k) (by omega)
      have hidx : N + (k + 1) = (N + k) + 1 := by omega
      rw [hidx, doublePower_succ 2 k, doublePower_succ (2 * a N) k]
      constructor
      · have hsq := Nat.mul_le_mul ih.1 ih.1
        nlinarith [hq.1]
      · have hsq := Nat.mul_le_mul ih.2 ih.2
        nlinarith [hq.2]

/-- An arbitrary positive ratio-one sequence has a global geometric
majorant, including its finite prefix. -/
theorem positive_ratio_one_geometric_envelope
    (U : ℕ → ℕ) (hU : ∀ n, 0 < U n)
    (hlim : Tendsto (fun n ↦ (U (n + 1) : ℝ) / (U n : ℝ)) atTop (𝓝 1))
    (r : ℝ) (hr : 1 < r) :
    ∃ K : ℝ, 0 < K ∧ (∀ n : ℕ, (U n : ℝ) ≤ K * r ^ n) ∧
      (∀ n : ℕ, (runningMax U n : ℝ) ≤ K * r ^ n) := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim (r - 1) (by linarith)
  have hstep : ∀ n, N ≤ n → (U (n + 1) : ℝ) ≤ r * (U n : ℝ) := by
    intro n hn
    have hh := hN n hn
    rw [Real.dist_eq] at hh
    have hratio : (U (n + 1) : ℝ) / (U n : ℝ) ≤ r := by
      have ht := (abs_lt.mp hh).2
      linarith
    have hpos : (0 : ℝ) < (U n : ℝ) := by exact_mod_cast hU n
    exact (div_le_iff₀ hpos).1 hratio
  let K : ℝ := (runningMax U N : ℝ)
  have hK : 0 < K := by
    have hu := hU N
    have hh := le_runningMax U (le_refl N)
    dsimp [K]
    exact_mod_cast (lt_of_lt_of_le hu hh)
  have hr0 : 0 ≤ r := by linarith
  have hpowers : ∀ n : ℕ, 1 ≤ r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have hmul := mul_le_mul_of_nonneg_left hr.le (pow_nonneg hr0 n)
        nlinarith
  have hu : ∀ n : ℕ, (U n : ℝ) ≤ K * r ^ n := by
    intro n
    induction n with
    | zero =>
        have hh := le_runningMax U (Nat.zero_le N)
        have hh' : (U 0 : ℝ) ≤ K := by
          dsimp [K]
          exact_mod_cast hh
        simpa only [pow_zero, mul_one] using hh'
    | succ n ih =>
        by_cases hn : N ≤ n
        · calc
            (U (n + 1) : ℝ) ≤ r * (U n : ℝ) := hstep n hn
            _ ≤ r * (K * r ^ n) := mul_le_mul_of_nonneg_left ih hr0
            _ = K * r ^ (n + 1) := by rw [pow_succ]; ring
        · have hprefix : (U (n + 1) : ℝ) ≤ K := by
            dsimp [K]
            exact_mod_cast (le_runningMax U (show n + 1 ≤ N by omega))
          have hmul := mul_le_mul_of_nonneg_left (hpowers (n + 1)) hK.le
          nlinarith
  refine ⟨K, hK, hu, ?_⟩
  intro n
  induction n with
  | zero => exact hu 0
  | succ n ih =>
      have hnext := hu (n + 1)
      have hmono : K * r ^ n ≤ K * r ^ (n + 1) := by
        rw [pow_succ]
        have hmul := mul_le_mul_of_nonneg_left hr.le (mul_nonneg hK.le (pow_nonneg hr0 n))
        nlinarith
      have hmax : ((max (runningMax U n) (U (n + 1)) : ℕ) : ℝ) =
          max (runningMax U n : ℝ) (U (n + 1) : ℝ) := by push_cast; rfl
      change ((max (runningMax U n) (U (n + 1)) : ℕ) : ℝ) ≤ _
      rw [hmax]
      exact max_le (ih.trans hmono) hnext

/-- The ratio-one premise in the preceding theorem is itself supplied from
the canonical rational reciprocal series. -/
theorem canonical_numerator_ratio_tendsto_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) :
    Tendsto (fun n ↦ (canonicalNaturalNumerator a p q (n + 1) : ℝ) /
      (canonicalNaturalNumerator a p q n : ℝ)) atTop (𝓝 1) := by
  have h := scaled_reciprocal_tail_ratio_tendsto_one a ha hapos hs.summable hgrowth
  apply h.congr'
  exact Eventually.of_forall fun n ↦ (canonical_numerator_ratio_eq a hapos p q hq hs n).symm

/-- An arbitrarily slow global envelope for both C and its actual running
maximum.  This is the required uniform version, not a pointwise estimate
at a selected index. -/
theorem canonical_runningMax_subexponential_envelope
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1)) (r : ℝ) (hr : 1 < r) :
    ∃ K : ℝ, 0 < K ∧
      (∀ n : ℕ, (canonicalNaturalNumerator a p q n : ℝ) ≤ K * r ^ n) ∧
      (∀ n : ℕ, (runningMax (canonicalNaturalNumerator a p q) n : ℝ) ≤ K * r ^ n) :=
  positive_ratio_one_geometric_envelope (canonicalNaturalNumerator a p q)
    (canonical_integer_tail a hapos p q hq hs).1
    (canonical_numerator_ratio_tendsto_one a ha hapos p q hq hs hgrowth) r hr

end ErdosProblems.Erdos243.PaperCompleteR11


