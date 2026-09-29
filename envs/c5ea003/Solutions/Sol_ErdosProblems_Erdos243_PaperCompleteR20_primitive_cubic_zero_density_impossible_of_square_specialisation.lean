-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR20.primitive_cubic_zero_density_impossible_of_square_specialisation
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:10:02.751817+00:00
-- url     : https://prove2.me/submissions/9b417fe5-02c5-49ec-a33e-fd7dfcdc03d4

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicSquareCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicFieldCoordinates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicIntegralNormalisation
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticWindows
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicQuarticCertificates
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CubicZeroDensityShape
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_ZeroLowerDensity_not_positive_lower_bound
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_cubic_scale_twelve_of_square_in_adjoin
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_integral_cubic_mod_seven_quartic_density
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_primitive_zero_density_multiplier_irreducibility
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.RingTheory.PowerBasis
import Mathlib.Tactic
import Mathlib.Tactic.Ring

namespace ErdosProblems.Erdos243.PaperCompleteR20
end ErdosProblems.Erdos243.PaperCompleteR20

/-!
# Erdős 243: the exact post-specialisation cubic contradiction

This module isolates the part of the fixed-cubic exclusion after the number-
field specialisation.  Starting from the actual primitive positive orbit and
zero lower density of failures, the existing arithmetic develops the unit
constant and irreducibility.  If the Chebotarev specialisation has produced
the required square in the cubic root field, the algebraic classification
forces scale twelve, and the explicit modulo-seven certificate contradicts
zero lower density.

The square-specialisation hypothesis is the precise remaining number-field
input.  It is not a reformulation of the density conclusion.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20
open ErdosProblems.Erdos243.PaperCompleteR11
open Polynomial
end ErdosProblems.Erdos243.PaperCompleteR20

open ErdosProblems.Erdos243.PaperCompleteR11
open Polynomial
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR20 in
theorem solution
    {L : Type*} [Field L] [Algebra ℚ L]
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (α β : L)
    (hroot : α ^ 3 = α - algebraMap ℚ L (6 * (c : ℚ) / (m : ℚ)))
    (hβmem : β ∈ IntermediateField.adjoin ℚ ({α} : Set L))
    (hβ : β ^ 2 = α ^ 2 - 1) : False := by
  obtain ⟨hc, _hcd, _hpair, _hlate, _hprimes, hirr⟩ :=
    primitive_zero_density_multiplier_irreducibility
      a u v m c T hm hv hnum hden hcop hzero
  have hcQ : (c : ℚ) = 1 ∨ (c : ℚ) = -1 := by
    rcases hc with rfl | rfl <;> norm_num
  have hm12 : m = 12 :=
    cubic_scale_twelve_of_square_in_adjoin m (c : ℚ) hm hcQ
      α β hirr hroot hβmem hβ
  have hnumZ : ∀ n, T ≤ n →
      (u (n + 1) : ℤ) + (v n : ℤ) = (a n : ℤ) * (u n : ℤ) := by
    intro n hn
    exact_mod_cast hnum n hn
  have hdenZ : ∀ n, T ≤ n →
      (v (n + 1) : ℤ) = (a n : ℤ) * (v n : ℤ) := by
    intro n hn
    exact_mod_cast hden n hn
  subst m
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hratio : (c : ZMod 7) / (12 : ZMod 7) = 1 ∨
      (c : ZMod 7) / (12 : ZMod 7) = 3 ∨
      (c : ZMod 7) / (12 : ZMod 7) = 4 ∨
      (c : ZMod 7) / (12 : ZMod 7) = 6 := by
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inl (by decide))
    · exact Or.inr (Or.inr (Or.inl (by decide)))
  have hdensity := integral_cubic_mod_seven_quartic_density
    (fun n ↦ (a n : ℤ)) (fun n ↦ (u n : ℤ)) (fun n ↦ (v n : ℤ))
    12 c T hnumZ hdenZ (by decide) hratio
  exact (hzero.not_positive_lower_bound (1 / 7) (by norm_num)) hdensity
