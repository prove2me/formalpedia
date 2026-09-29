-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_InclusiveRecordAssembly_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_InclusiveRecordAssembly_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:55:12.432588+00:00
-- url     : https://prove2.me/theorems/bb565771-519a-49ed-92c5-75c894d1f999
-- title:
--   Canonical record-growth assembly
-- statement:
--   Contains source-proved construction of the canonical record-growth orbit from a nonsylvester rational reciprocal sequence and its unboundedness. It prepares, but does not itself state, the inclusive log-log endpoint.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR11/InclusiveRecordAssembly.lean#L1-L204
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR11_InclusiveRecordAssembly_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR11.InclusiveRecordAssembly.

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
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_OrbitBlockArithmetic_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_PresievedCRT_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_RecordGcdReduction_v243UnionFbf41fb8
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Inclusive coefficient-one record boundary


The exact conclusion is a fixed coefficient c>1 exceeded cofinally at
strict global records. This implies the paper's strict limsup inequality;
the separate extended-real presentation is not used in this proof.
Both gcd alternatives are handled by constructed quotient tails.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

open PaperCompleteR7 Filter
open scoped Topology







/-- With normalised integer vanishing, a bounded canonical numerator
forces exact eventual Sylvester recursion; no bounded-error assumption is added. -/
theorem canonical_unbounded_of_not_sylvester
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    ∀ H : ℕ, ∃ n, H ≤ canonicalNaturalNumerator a p q n := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  obtain ⟨hCpos, hDpos, hC, hD, htail, hvanish, hcentred⟩ :=
    canonical_integer_tail_normalized a ha hapos p q hq hs hgrowth
  intro H
  by_contra hno
  have hbound : ∀ n, C n < H := by
    intro n
    by_contra hn
    exact hno ⟨n, le_of_not_gt hn⟩
  obtain ⟨N, hN⟩ := hvanish H
  have hzero : ∀ n, N ≤ n → E n = 0 := by
    intro n hn
    by_contra hne
    have habs : 1 ≤ Int.natAbs (E n) := by
      have hh := Int.natAbs_pos.mpr hne
      omega
    have hmul := Nat.mul_le_mul_left H habs
    have hh : H * Int.natAbs (E n) < C n := hN n hn
    have hb := hbound n
    omega
  apply hnot
  apply sylvesterNext_eventually_of_centered_zero
    (fun n ↦ (a n : ℤ)) (fun n ↦ (D n : ℤ)) (fun n ↦ (C n : ℤ))
  · intro n
    exact natDen_eq_nextDenState a D hD n
  · intro n
    exact natTail_eq_nextTailState a C D hC n
  · exact ⟨N, hzero⟩
  · exact ⟨0, fun n _ ↦ by exact_mod_cast (hCpos (n + 1)).ne'⟩

/-- Canonical construction from the paper's original hypotheses alone. -/
noncomputable def canonicalRecordGrowthOrbit
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    RecordGrowthOrbit := by
  have htail := canonical_integer_tail a hapos p q hq hs
  refine {
    a := a, U := canonicalNaturalNumerator a p q, D := canonicalDenominator a q
    increasing := ha, a_pos := hapos, U_pos := htail.1, D_pos := htail.2.1
    U_step := htail.2.2.1, D_step := htail.2.2.2.1
    lower := ?_
    record_bound := canonical_runningMax_binary_exponent a ha hapos p q hq hs hgrowth
    den_bound := canonical_denominator_binaryTower_bound a ha hapos q hgrowth
    unbounded := canonical_unbounded_of_not_sylvester a ha hapos p q hq hs hgrowth hnot }
  obtain ⟨N, A, hN, hA, hbounds⟩ := quadratic_double_exponential_bounds a ha hapos hgrowth
  exact ⟨N, fun k ↦ (hbounds k).1⟩



end ErdosProblems.Erdos243.PaperCompleteR11


