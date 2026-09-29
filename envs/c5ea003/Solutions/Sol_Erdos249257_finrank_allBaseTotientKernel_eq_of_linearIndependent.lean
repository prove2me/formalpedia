-- Prove2me | solution 1 for Erdos249257.finrank_allBaseTotientKernel_eq_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T13:55:16.311386+00:00
-- url     : https://prove2.me/submissions/bef8bb6a-45a8-4d17-819c-08de4c09fe3a

import Definitions.Def_Erdos249257_TotientKernelIndex
import Definitions.Def_Erdos249257_TotientKernelConditional
import Definitions.Def_Erdos249257_TotientMahlerDefect
import Definitions.Def_Erdos249257_AllBaseTotientKernel
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimesCongruentOne

namespace Erdos249257
open Module Matrix
theorem card_allBaseCanonicalIndex (k e : ℕ) (hk : 1 ≤ k) :
    Fintype.card (AllBaseCanonicalIndex k e) = k ^ e + 1 := by
  have key : ∀ m : ℕ, (∑ j ∈ Finset.range m, k ^ j * (k - 1)) + 1 = k ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, add_right_comm, ih]
        have hstep : 1 + (k - 1) = k := by omega
        calc k ^ m + k ^ m * (k - 1) = k ^ m * (1 + (k - 1)) := by ring
          _ = k ^ m * k := by rw [hstep]
          _ = k ^ (m + 1) := by ring
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun j => k ^ j * (k - 1)) e]
  have hk' := key e
  omega
end Erdos249257

open Erdos249257
open Module Matrix
open Erdos249257 in
theorem solution (k e : ℕ) (hk : 2 ≤ k)
    (hli : LinearIndependent ℚ (allBaseCanonicalFamily k e)) :
    finrank ℚ (Submodule.span ℚ (Set.range (allBaseCanonicalFamily k e))) =
      k ^ e + 1 := by
  rw [finrank_span_eq_card hli]
  exact card_allBaseCanonicalIndex k e (by omega)
