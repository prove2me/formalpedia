-- Prove2me | solution 1 for ErdosProblems.Erdos243.LcmRecordCrossing.covering_of_crt_block
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:48:21.495914+00:00
-- url     : https://prove2.me/submissions/bc49c5a7-e722-4226-b95a-84f20d402dc0

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

namespace LcmRecordExcess
end LcmRecordExcess

/-!
# Counting the CRT heights crossed by one arithmetic step

The heights are the actual arithmetic progression `x + k * P`, not an
assumed cardinality bound. This supplies the finite local charging step in
the weighted-record argument of `LcmRecordExcess.md`. First-crossing existence,
uniqueness, and the finite partition across time require no monotonicity of
the numerator sequence. The existing CRT construction supplies the covering
from any finite family of sufficiently large pairwise-coprime old divisors.
Producing that family from an infinite canonical orbit and the analytic
divergence argument are not asserted by this module.
-/

namespace ErdosProblems.Erdos243.LcmRecordCrossing
open LcmRecordExcess
end ErdosProblems.Erdos243.LcmRecordCrossing

open LcmRecordExcess
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.LcmRecordCrossing in
open ErdosProblems.Erdos243.LcmRecordExcess in
theorem solution {B : ℕ} (m : Fin B → ℕ)
    (x P k : ℕ) (L : ℤ)
    (hm : ∀ i, B < m i) (hmP : ∀ i, m i ∣ P)
    (hmL : ∀ i, (m i : ℤ) ∣ L)
    (hresidue : ∀ i, m i ∣ x + i.1) :
    ∀ z : ℤ, (x + B + k * P : ℕ) - (B : ℤ) ≤ z →
      z < (x + B + k * P : ℕ) →
      ∃ d : ℤ, (B : ℤ) < d ∧ d ∣ L ∧ d ∣ z := by
  intro z hlo hhi
  let base := x + k * P
  have hwall : x + B + k * P = base + B := by dsimp [base]; omega
  rw [hwall] at hlo hhi
  have hnonneg : 0 ≤ z - (base : ℤ) := by omega
  have hindex : (z - (base : ℤ)).toNat < B := by omega
  let i : Fin B := ⟨(z - (base : ℤ)).toNat, hindex⟩
  have hi : (i.1 : ℤ) = z - (base : ℤ) := by
    dsimp [i]
    exact Int.toNat_of_nonneg hnonneg
  have hz : z = ((x + i.1 : ℕ) : ℤ) + ((k * P : ℕ) : ℤ) := by
    calc
      z = (base : ℤ) + (i.1 : ℤ) := by omega
      _ = _ := by dsimp [base]; ring
  refine ⟨m i, by exact_mod_cast hm i, hmL i, ?_⟩
  rw [hz]
  exact dvd_add (Int.natCast_dvd_natCast.mpr (hresidue i))
    (Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_right (hmP i) k))
