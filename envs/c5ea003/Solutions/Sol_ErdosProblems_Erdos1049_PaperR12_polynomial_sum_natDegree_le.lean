-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.polynomial_sum_natDegree_le
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:17:21.090697+00:00
-- url     : https://prove2.me/submissions/644f4d0c-cf20-43a1-96b5-16645c31bced

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
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
# Exact Gaussian and actual A degrees


The unique highest summand is proved at every index; finite reconstructions
are not used to infer a polynomial identity. The integer coefficient mass of
each Gaussian is also evaluated exactly, rather than bounding one coefficient
and silently treating that as an l1 bound.
-/

namespace ErdosProblems.Erdos1049.PaperR12
open Polynomial
open PaperR11
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR12

open Polynomial
open PaperR11
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR12 in
open ErdosProblems.Erdos1049.PaperR11 in
theorem solution {ι : Type*} (s : Finset ι)
    (p : ι → ℤ[X]) (d : ℕ) (h : ∀ i ∈ s, (p i).natDegree ≤ d) :
    (∑ i ∈ s, p i).natDegree ≤ d := by
  apply natDegree_le_of_degree_le
  apply (degree_le_iff_coeff_zero _ _).2
  intro j hj
  have hj' : d < j := by exact_mod_cast hj
  rw [finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  exact coeff_eq_zero_of_natDegree_lt ((h i hi).trans_lt hj')
