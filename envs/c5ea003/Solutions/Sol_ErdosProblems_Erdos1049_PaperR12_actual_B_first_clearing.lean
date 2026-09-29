-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.actual_B_first_clearing
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:03:08.921681+00:00
-- url     : https://prove2.me/submissions/ca481c16-c40c-4277-8f56-af6276f7a5b5

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceDQuotient_factor
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceShiftedASummand_map
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic

namespace PaperR11
end PaperR11

/-!
# Literal B coefficient and its first polynomial clearing


This constructs the finite source expression itself, including its negative
powers, and proves D*B is an integral polynomial. It does NOT claim the
additional X^M or Omega cancellation. No polynomial-inclusion hypothesis is
used in the construction or the clearing theorem.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open scoped BigOperators
open PaperR11

















lemma sourceDQuotient_map {K : Type*} [Field K]
    (f : ℤ[X] →+* K) (n j : ℕ) (hj0 : 0 < j) (hj : j ≤ 15 * n)
    (hden : (f X) ^ j - 1 ≠ 0) :
    f (sourceDQuotient n j) = f (sourceD n) * ((f X) ^ j - 1)⁻¹ := by
  have h := congrArg f (sourceDQuotient_factor n j hj0 hj)
  simp only [map_mul, map_sub, map_pow, map_one] at h
  apply mul_right_cancel₀ hden
  calc
    f (sourceDQuotient n j) * ((f X) ^ j - 1) = f (sourceD n) := by
      simpa only [mul_comm] using h
    _ = (f (sourceD n) * ((f X) ^ j - 1)⁻¹) * ((f X) ^ j - 1) := by
      rw [mul_assoc, inv_mul_cancel₀ hden, mul_one]
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open scoped BigOperators
open PaperR11
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution {K : Type*} [Field K]
    (f : ℤ[X] →+* K) (n : ℕ) (hx : f X ≠ 0)
    (hden : ∀ j ∈ Finset.Icc 1 (15 * n), (f X) ^ j - 1 ≠ 0) :
    f (sourceClearedB n) = f (sourceD n) * sourceBValue f n := by
  classical
  unfold sourceClearedB sourceBValue
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hs' : s ≤ 13 * n := by have h := Finset.mem_range.mp hs; omega
  have hfirst :
      f (∑ l ∈ Finset.Icc 1 (2 * n + s),
        sourceASummand n s * sourceDQuotient n l) =
      f (sourceD n) * (f (sourceASummand n s) *
        ∑ l ∈ Finset.Icc 1 (2 * n + s), ((f X) ^ l - 1)⁻¹) := by
    simp only [map_sum, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    obtain ⟨hl0, hl1⟩ := Finset.mem_Icc.mp hl
    have hlN : l ≤ 15 * n := by omega
    rw [sourceDQuotient_map f n l hl0 hlN (hden l (Finset.mem_Icc.mpr ⟨hl0, hlN⟩))]
    ring
  have hsecond :
      f (∑ j ∈ Finset.Icc 1 (14 * n),
        sourceShiftedASummand n s j * sourceDQuotient n j) =
      f (sourceD n) * (f (sourceASummand n s) *
        ∑ j ∈ Finset.Icc 1 (14 * n),
          (f X) ^ (-((j * (2 * n + s) : ℕ) : ℤ)) * ((f X) ^ j - 1)⁻¹) := by
    simp only [map_sum, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨hj0, hj1⟩ := Finset.mem_Icc.mp hj
    have hjN : j ≤ 15 * n := by omega
    rw [sourceShiftedASummand_map f n s j hs' hj1 hx,
      sourceDQuotient_map f n j hj0 hjN (hden j (Finset.mem_Icc.mpr ⟨hj0, hjN⟩))]
    ring
  rw [map_add, hfirst, hsecond]
  ring
