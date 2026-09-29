-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.actual_V_quotient_degree
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:46:52.803868+00:00
-- url     : https://prove2.me/submissions/b1d15c68-fe07-4fc3-9398-2ebb196a065f

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceComplement_monic_degree
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_actual_U_degree
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_sourceK_gt_M
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR11_sourceD_factor
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_actual_B_without_monomial_degree_and_leadingCoeff
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_sourceOmega_monic
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

namespace PaperR12
end PaperR12

/-!
# Exact top degree of the literal cleared B numerator



The unique leading term is the unshifted pair (s,l)=(13*n,1).
This is a finite polynomial proof: neither A*F-B=H nor Omega divisibility
is an assumption. The canonical monic quotient V is defined even before
its remainder is known to vanish; its degree is not misrepresented as
proof that this remainder vanishes.
-/

namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12
open scoped BigOperators













lemma sourceD_degree_split (n : ℕ) :
    (sourceD n).natDegree =
      (sourceOmega n).natDegree + (sourceComplement n).natDegree := by
  rw [sourceD_factor]
  exact natDegree_mul' (by
    simp [(sourceOmega_monic n).leadingCoeff,
      (sourceComplement_monic_degree n).1.leadingCoeff])
end ErdosProblems.Erdos1049.PaperR13

open Polynomial PaperR11 PaperR12
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (sourceV n).natDegree = (sourceU n).natDegree - 1 := by
  unfold sourceV
  rw [natDegree_divByMonic _ (sourceOmega_monic n),
    (actual_B_without_monomial_degree_and_leadingCoeff n hn).1,
    actual_U_degree]
  have hsplit := sourceD_degree_split n
  have hc := (sourceComplement_monic_degree n).2
  have hk := sourceK_gt_M n hn
  unfold sourceClearedBTop
  omega
