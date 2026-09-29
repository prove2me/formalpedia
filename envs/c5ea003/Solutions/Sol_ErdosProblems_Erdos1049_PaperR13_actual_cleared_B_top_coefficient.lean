-- Prove2me | solution 1 for ErdosProblems.Erdos1049.PaperR13.actual_cleared_B_top_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T21:39:35.682718+00:00
-- url     : https://prove2.me/submissions/30a2034b-e161-445d-8b54-825e7c6e8caf

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
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceASummandDegree_last
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceASummandDegree_strict
import Theorems.Thm_ErdosProblems_Erdos1049_gaussBinom_zero_succ
import Theorems.Thm_ErdosProblems_Erdos1049_qPochhammer_zero
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceASummand_degree_and_leadingCoeff
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR13_sourceK_gt_M
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceDQuotient_factor
import Theorems.Thm_ErdosProblems_Erdos1049_PaperR12_sourceShiftedASummand_factor
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

lemma monic_finset_product {ι : Type*} (s : Finset ι) (p : ι → ℤ[X])
    (hp : ∀ i ∈ s, (p i).Monic) : (∏ i ∈ s, p i).Monic := by
  classical
  revert hp
  induction s using Finset.induction_on with
  | empty => intro hp; simp
  | @insert i s his ih =>
      intro hp
      rw [Finset.prod_insert his]
      exact (hp i (Finset.mem_insert_self i s)).mul
        (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))







lemma sourceDQuotient_monic (n j : ℕ) : (sourceDQuotient n j).Monic := by
  unfold sourceDQuotient
  exact monic_finset_product _ _ (fun l _ => cyclotomic.monic l ℤ)





lemma sourceDQuotient_degree_add (n j : ℕ) (hj0 : 0 < j) (hj : j ≤ 15 * n) :
    j + (sourceDQuotient n j).natDegree = (sourceD n).natDegree := by
  have h := congrArg Polynomial.natDegree (sourceDQuotient_factor n j hj0 hj)
  have hm : (X ^ j - 1 : ℤ[X]).Monic := by
    simpa using monic_X_pow_sub_C (1 : ℤ) hj0.ne'
  rw [natDegree_mul' (by
    simp [hm.leadingCoeff, (sourceDQuotient_monic n j).leadingCoeff])] at h
  change (X ^ j - C (1 : ℤ)).natDegree + (sourceDQuotient n j).natDegree =
    (sourceD n).natDegree at h
  rw [natDegree_X_pow_sub_C] at h
  exact h

lemma sourceASummand_ne_zero (n s : ℕ) (hs : s ≤ 13 * n) :
    sourceASummand n s ≠ 0 := by
  apply leadingCoeff_ne_zero.mp
  rw [(sourceASummand_degree_and_leadingCoeff n s hs).2]
  exact pow_ne_zero _ (by norm_num)

lemma sourceShiftedASummand_ne_zero (n s j : ℕ) (hs : s ≤ 13 * n)
    (hj : j ≤ 14 * n) : sourceShiftedASummand n s j ≠ 0 := by
  intro hz
  have h := sourceShiftedASummand_factor n s j hs hj
  rw [hz, mul_zero] at h
  exact sourceASummand_ne_zero n s hs h.symm

lemma sourceShiftedASummand_degree_add (n s j : ℕ) (hs : s ≤ 13 * n)
    (hj : j ≤ 14 * n) :
    j * (2 * n + s) + (sourceShiftedASummand n s j).natDegree =
      sourceASummandDegree n s := by
  have h := congrArg Polynomial.natDegree (sourceShiftedASummand_factor n s j hs hj)
  rw [natDegree_mul' (by
      simpa only [leadingCoeff_X_pow, one_mul] using
        leadingCoeff_ne_zero.mpr (sourceShiftedASummand_ne_zero n s j hs hj)),
    natDegree_X_pow, (sourceASummand_degree_and_leadingCoeff n s hs).1] at h
  exact h

lemma sourceASummandDegree_le_K (n s : ℕ) (hs : s ≤ 13 * n) :
    sourceASummandDegree n s ≤ sourceK n := by
  rw [← sourceASummandDegree_last n]
  rcases lt_or_eq_of_le hs with hlt | rfl
  · exact (sourceASummandDegree_strict n hlt le_rfl).le
  · exact le_rfl





lemma sourceClearedBTop_add_one (n : ℕ) (hn : 1 ≤ n) :
    sourceClearedBTop n + 1 = (sourceD n).natDegree + sourceK n := by
  have hk := sourceK_gt_M n hn
  unfold sourceClearedBTop
  omega

lemma sourceB_first_term_degree_add (n s l : ℕ) (hs : s ≤ 13 * n)
    (hl0 : 0 < l) (hl : l ≤ 15 * n) :
    (sourceASummand n s * sourceDQuotient n l).natDegree + l =
      sourceASummandDegree n s + (sourceD n).natDegree := by
  rw [natDegree_mul' (by
    simpa only [(sourceDQuotient_monic n l).leadingCoeff, mul_one] using
      leadingCoeff_ne_zero.mpr (sourceASummand_ne_zero n s hs)),
    (sourceASummand_degree_and_leadingCoeff n s hs).1]
  have h := sourceDQuotient_degree_add n l hl0 hl
  omega



lemma sourceB_first_term_lt (n s l : ℕ) (hn : 1 ≤ n) (hs : s ≤ 13 * n)
    (hl0 : 0 < l) (hl : l ≤ 15 * n) (hne : s ≠ 13 * n ∨ l ≠ 1) :
    (sourceASummand n s * sourceDQuotient n l).natDegree < sourceClearedBTop n := by
  have h := sourceB_first_term_degree_add n s l hs hl0 hl
  have hk := sourceASummandDegree_le_K n s hs
  have htop := sourceClearedBTop_add_one n hn
  rcases hne with hsne | hlne
  · have hlt : sourceASummandDegree n s < sourceK n := by
      rw [← sourceASummandDegree_last n]
      exact sourceASummandDegree_strict n (by omega) le_rfl
    omega
  · omega

lemma sourceB_shifted_term_lt (n s j : ℕ) (hn : 1 ≤ n) (hs : s ≤ 13 * n)
    (hj0 : 0 < j) (hj : j ≤ 14 * n) :
    (sourceShiftedASummand n s j * sourceDQuotient n j).natDegree < sourceClearedBTop n := by
  rw [natDegree_mul' (by
    simpa only [(sourceDQuotient_monic n j).leadingCoeff, mul_one] using
      leadingCoeff_ne_zero.mpr (sourceShiftedASummand_ne_zero n s j hs hj))]
  have hshift := sourceShiftedASummand_degree_add n s j hs hj
  have hquot := sourceDQuotient_degree_add n j hj0 (by omega)
  have hk := sourceASummandDegree_le_K n s hs
  have htop := sourceClearedBTop_add_one n hn
  have hpos : 0 < j * (2 * n + s) := Nat.mul_pos hj0 (by omega)
  omega

lemma sourceB_top_term_degree_and_leadingCoeff (n : ℕ) (hn : 1 ≤ n) :
    (sourceASummand n (13 * n) * sourceDQuotient n 1).natDegree = sourceClearedBTop n ∧
    (sourceASummand n (13 * n) * sourceDQuotient n 1).leadingCoeff = (-1 : ℤ) ^ (13 * n) := by
  constructor
  · have h := sourceB_first_term_degree_add n (13 * n) 1 le_rfl (by omega) (by omega)
    rw [sourceASummandDegree_last] at h
    have htop := sourceClearedBTop_add_one n hn
    omega
  · rw [leadingCoeff_mul,
      (sourceASummand_degree_and_leadingCoeff n (13 * n) le_rfl).2,
      (sourceDQuotient_monic n 1).leadingCoeff, mul_one]
end ErdosProblems.Erdos1049.PaperR13

open Polynomial PaperR11 PaperR12
open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos1049 in
open ErdosProblems.Erdos1049.PaperR13 in
open ErdosProblems.Erdos1049.PaperR11 in
open ErdosProblems.Erdos1049.PaperR12 in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (sourceClearedB n).coeff (sourceClearedBTop n) = (-1 : ℤ) ^ (13 * n) := by
  classical
  unfold sourceClearedB
  rw [finset_sum_coeff]
  rw [Finset.sum_eq_single (13 * n)]
  · rw [coeff_add, finset_sum_coeff, finset_sum_coeff]
    have hshift : (∑ j ∈ Finset.Icc 1 (14 * n),
        (sourceShiftedASummand n (13 * n) j * sourceDQuotient n j).coeff
          (sourceClearedBTop n)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact coeff_eq_zero_of_natDegree_lt (sourceB_shifted_term_lt n (13 * n) j hn
        le_rfl (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)
    rw [hshift, add_zero, Finset.sum_eq_single 1]
    · obtain ⟨hd, hc⟩ := sourceB_top_term_degree_and_leadingCoeff n hn
      rw [← hd, coeff_natDegree, hc]
    · intro l hl hne
      exact coeff_eq_zero_of_natDegree_lt (sourceB_first_term_lt n (13 * n) l hn
        le_rfl (Finset.mem_Icc.mp hl).1 (by have h := (Finset.mem_Icc.mp hl).2; omega)
        (Or.inr hne))
    · intro hnot
      exact (hnot (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)).elim
  · intro s hs hne
    have hs' : s ≤ 13 * n := by have h := Finset.mem_range.mp hs; omega
    rw [coeff_add, finset_sum_coeff, finset_sum_coeff]
    have hfirst : (∑ l ∈ Finset.Icc 1 (2 * n + s),
        (sourceASummand n s * sourceDQuotient n l).coeff (sourceClearedBTop n)) = 0 := by
      apply Finset.sum_eq_zero
      intro l hl
      exact coeff_eq_zero_of_natDegree_lt (sourceB_first_term_lt n s l hn hs'
        (Finset.mem_Icc.mp hl).1 (by have h := (Finset.mem_Icc.mp hl).2; omega)
        (Or.inl hne))
    have hshift : (∑ j ∈ Finset.Icc 1 (14 * n),
        (sourceShiftedASummand n s j * sourceDQuotient n j).coeff (sourceClearedBTop n)) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact coeff_eq_zero_of_natDegree_lt (sourceB_shifted_term_lt n s j hn hs'
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2)
    rw [hfirst, hshift, zero_add]
  · intro hnot
    exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim
