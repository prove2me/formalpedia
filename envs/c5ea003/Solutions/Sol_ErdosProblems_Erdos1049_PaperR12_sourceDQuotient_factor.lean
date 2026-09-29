-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceDQuotient_factor
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:34:07.075093+00:00
-- url     : https://prove2.me/submissions/87cddfbb-47cc-432c-9a10-a5c9ce8c59db

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
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



lemma source_divisors_subset (n j : ℕ) (hj0 : 0 < j) (hj : j ≤ 15 * n) :
    j.divisors ⊆ Finset.Icc 1 (15 * n) := by
  intro l hl
  apply Finset.mem_Icc.mpr
  exact ⟨Nat.pos_of_mem_divisors hl,
    (Nat.le_of_dvd hj0 (Nat.mem_divisors.mp hl).1).trans hj⟩
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open scoped BigOperators
open PaperR11
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n j : ℕ) (hj0 : 0 < j) (hj : j ≤ 15 * n) :
    (X ^ j - 1 : ℤ[X]) * sourceDQuotient n j = sourceD n := by
  classical
  have hs := source_divisors_subset n j hj0 hj
  rw [sourceDQuotient, sourceD, ← prod_cyclotomic_eq_X_pow_sub_one hj0 ℤ]
  rw [mul_comm, ← Finset.prod_union Finset.sdiff_disjoint,
    Finset.sdiff_union_of_subset hs]
