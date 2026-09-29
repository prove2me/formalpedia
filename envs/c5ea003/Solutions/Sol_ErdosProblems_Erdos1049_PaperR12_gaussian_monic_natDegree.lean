-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR12.gaussian_monic_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T18:23:52.819292+00:00
-- url     : https://prove2.me/submissions/fa27feb8-006d-4681-9dce-4d04724655ba

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_self
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_succ_of_le
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_right
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
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
theorem solution (n k : ℕ) (hk : k ≤ n) :
    (gaussBinom (X : ℤ[X]) n k).Monic ∧
      (gaussBinom (X : ℤ[X]) n k).natDegree = k * (n - k) := by
  induction n generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp [gaussBinom]
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := by omega
          by_cases heq : k = n
          · subst k
            simp [gaussBinom_self]
          · have hlt : k < n := by omega
            obtain ⟨hL, hdL⟩ := ih (k + 1) (by omega)
            obtain ⟨hG, hdG⟩ := ih k hkn
            have hR : ((X : ℤ[X]) ^ (n - k) * gaussBinom X n k).Monic :=
              (monic_X_pow (n - k)).mul hG
            have hdR : ((X : ℤ[X]) ^ (n - k) * gaussBinom X n k).natDegree =
                (n - k) + k * (n - k) := by
              rw [natDegree_mul' (by simp [hG.leadingCoeff]), natDegree_X_pow, hdG]
            have hsub : n - (k + 1) + 1 = n - k := by omega
            have hdeglt : (gaussBinom (X : ℤ[X]) n (k + 1)).natDegree <
                ((X : ℤ[X]) ^ (n - k) * gaussBinom X n k).natDegree := by
              rw [hdL, hdR]
              nlinarith
            rw [gaussBinom_succ_of_le X hkn]
            constructor
            · change (_ + _ : ℤ[X]).leadingCoeff = 1
              rw [leadingCoeff_add_of_degree_lt (degree_lt_degree hdeglt), hR.leadingCoeff]
            · rw [natDegree_add_eq_right_of_natDegree_lt hdeglt, hdR]
              have hsub' : n + 1 - (k + 1) = n - k := by omega
              rw [hsub']
              ring
