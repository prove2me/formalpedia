-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.finite_prefix_supported_on_multiples
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:27:43.746412+00:00
-- url     : https://prove2.me/submissions/858e94f4-ebb8-41d6-9ad1-2246cbb33344

import Definitions.Def_ErdosProblems_Erdos1049_QBinomialUnitIdentity
import Definitions.Def_ErdosProblems_Erdos1049_ZudilinConeArithmetic
import Definitions.Def_ErdosProblems_Erdos1049_PaperOmegaIndicatorR7
import Definitions.Def_ErdosProblems_Erdos1049_SourcePolynomialR11
import Definitions.Def_ErdosProblems_Erdos1049_SourceBClearingR12
import Definitions.Def_ErdosProblems_Erdos1049_GaussianDegreeR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceFiniteTransformR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceHomogeneousR12
import Definitions.Def_ErdosProblems_Erdos1049_RootUnityLocalCancellationR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceBMonomialR12
import Definitions.Def_ErdosProblems_Erdos1049_SourceBTopDegreeR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootCarriesR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceRootBlocksR13
import Definitions.Def_ErdosProblems_Erdos1049_SourceOmegaCancellationR13
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

namespace PaperR12
end PaperR12

namespace ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators
end ErdosProblems.Erdos1049.PaperR13

open ErdosProblems
open ErdosProblems.Erdos1049
open ErdosProblems.Erdos1049.PaperR13
open Polynomial PaperR11 PaperR12 Finset
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution {R : Type*} [AddCommMonoid R]
    (g : ℕ → R) (ell J : ℕ) (hell : 0 < ell)
    (hzero : ∀ j ∈ Icc 1 J, ¬ ell ∣ j → g j = 0) :
    (∑ j ∈ Icc 1 J, g j) = ∑ b ∈ Icc 1 (J / ell), g (ell * b) := by
  classical
  have hfilter : (∑ j ∈ (Icc 1 J).filter (fun j => ell ∣ j), g j) =
      ∑ j ∈ Icc 1 J, g j := by
    apply sum_subset (filter_subset _ _)
    intro j hj hnot
    apply hzero j hj
    intro hdiv
    exact hnot (mem_filter.mpr ⟨hj, hdiv⟩)
  rw [← hfilter]
  symm
  refine sum_bij (fun b _ => ell * b) ?_ ?_ ?_ ?_
  · intro b hb
    obtain ⟨hb0, hbJ⟩ := mem_Icc.mp hb
    apply mem_filter.mpr
    refine ⟨mem_Icc.mpr ⟨by nlinarith, ?_⟩, dvd_mul_right _ _⟩
    have hm := (Nat.le_div_iff_mul_le hell).mp hbJ
    simpa only [Nat.mul_comm b ell] using hm
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hell hab
  · intro j hj
    obtain ⟨hjI, hdiv⟩ := mem_filter.mp hj
    obtain ⟨b, rfl⟩ := hdiv
    refine ⟨b, mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · have hj0 := (mem_Icc.mp hjI).1
      by_contra hb
      have : b = 0 := by omega
      simp [this] at hj0
    · apply (Nat.le_div_iff_mul_le hell).mpr
      simpa only [Nat.mul_comm b ell] using (mem_Icc.mp hjI).2
  · intro b hb
    rfl
