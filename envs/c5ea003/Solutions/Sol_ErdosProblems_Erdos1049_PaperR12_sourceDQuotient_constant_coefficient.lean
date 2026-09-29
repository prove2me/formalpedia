-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.sourceDQuotient_constant_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:10:59.258548+00:00
-- url     : https://prove2.me/submissions/2a6eadd3-3c4c-4cc8-bc3f-da7592806f07

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
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
# Exact initial coefficient of the actual B numerator


The numerator is divisible by X^M but not X^(M+1): at every n>=1 its
coefficient at M is exactly 1. This is proved by isolating the actual j=n,
s=0 channel. No finite reconstruction or initial-order hypothesis is used.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial PaperR11
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR12

open Polynomial PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution (n j : ℕ) (hj : 0 < j) :
    (sourceDQuotient n j).coeff 0 = 1 := by
  classical
  change constantCoeff (sourceDQuotient n j) = 1
  simp only [sourceDQuotient, map_prod]
  apply Finset.prod_eq_one
  intro l hl
  obtain ⟨hlrange, hnot⟩ := Finset.mem_sdiff.mp hl
  have hlpos : 1 ≤ l := (Finset.mem_Icc.mp hlrange).1
  have hlne : l ≠ 1 := by
    intro he
    apply hnot
    rw [he]
    exact Nat.mem_divisors.mpr ⟨one_dvd _, ne_of_gt hj⟩
  exact cyclotomic_coeff_zero ℤ (show 2 ≤ l by omega)
