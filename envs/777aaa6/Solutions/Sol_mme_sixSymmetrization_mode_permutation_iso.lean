-- Prove2me | solution 1 for mme_sixSymmetrization_mode_permutation_iso
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T05:23:26.481535+00:00
-- url     : https://prove2.me/submissions/14e868d1-0ec1-4cfa-9376-3cda330df420

import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
import Theorems.Thm_mme_cyclicSymmetrization_isomorphic_cyclic_orbit
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Mathlib.Tactic.FinCases

open MME MME.TensorObj PiTensorProduct
universe u

private theorem perm_trans_eq {K : Type u} [Field K]
    (e f : Equiv.Perm (Fin 3)) (T : TensorObj K 3) :
    permObj f (permObj e T) = permObj (e.trans f) T := by
  unfold permObj
  congr 1
  exact reindex_reindex e f T.t

private theorem perm_refl_eq {K : Type u} [Field K] (T : TensorObj K 3) :
    permObj (Equiv.refl _) T = T := by
  cases T
  simp only [permObj, reindex_refl]
  rfl

private theorem cyclic_congr {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : Isomorphic X Y) : Isomorphic (cyclicSymmetrization X) (cyclicSymmetrization Y) :=
  ⟨mme_cyclicSymmetrization_mono_restrict h.1,
    mme_cyclicSymmetrization_mono_restrict h.2⟩

private theorem six_of_cyclic {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : Isomorphic (cyclicSymmetrization X) (cyclicSymmetrization Y)) :
    Isomorphic (sixSymmetrization X) (sixSymmetrization Y) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [sixSymmetrization, TensorQ.toQ_kron, ← TensorQ.permAut_toQ]
  rw [TensorQ.toQ_eq_iff.mpr h]

private theorem six_cycle {K : Type u} [Field K] (T : TensorObj K 3) :
    Isomorphic (sixSymmetrization (permObj cyclicPerm T)) (sixSymmetrization T) :=
  six_of_cyclic (mme_cyclicSymmetrization_isomorphic_cyclic_orbit T).1

private theorem six_swap {K : Type u} [Field K] (T : TensorObj K 3) :
    Isomorphic (sixSymmetrization (permObj swapFirstTwoPerm T)) (sixSymmetrization T) := by
  have hss : swapFirstTwoPerm.trans swapFirstTwoPerm = Equiv.refl (Fin 3) := by decide
  have hpair : Isomorphic
      (kron (permObj swapFirstTwoPerm T) (permObj swapFirstTwoPerm (permObj swapFirstTwoPerm T)))
      (kron T (permObj swapFirstTwoPerm T)) := by
    rw [perm_trans_eq, hss, perm_refl_eq]
    apply TensorQ.toQ_eq_iff.mp
    simp only [TensorQ.toQ_kron, mul_comm]
  exact (mme_sixSymmetrization_isomorphic_cyclic_paired_swap _).trans
    ((cyclic_congr hpair).trans (mme_sixSymmetrization_isomorphic_cyclic_paired_swap T).symm)

private theorem compose_invariant {K : Type u} [Field K]
    (e f : Equiv.Perm (Fin 3))
    (he : ∀ T : TensorObj K 3,
      Isomorphic (sixSymmetrization (permObj e T)) (sixSymmetrization T))
    (hf : ∀ T : TensorObj K 3,
      Isomorphic (sixSymmetrization (permObj f T)) (sixSymmetrization T))
    (T : TensorObj K 3) :
    Isomorphic (sixSymmetrization (permObj (e.trans f) T)) (sixSymmetrization T) := by
  rw [← perm_trans_eq]
  exact (hf (permObj e T)).trans (he T)

/-- Full six-fold symmetrization is unchanged, up to tensor isomorphism,
by any permutation of the original three modes. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) (sigma : Equiv.Perm (Fin 3)) :
    Isomorphic (sixSymmetrization (permObj sigma T)) (sixSymmetrization T) := by
  have hcc := compose_invariant cyclicPerm cyclicPerm (six_cycle (K := K)) six_cycle
  have hsc := compose_invariant swapFirstTwoPerm cyclicPerm (six_swap (K := K)) six_cycle
  have hscc := compose_invariant swapFirstTwoPerm (cyclicPerm.trans cyclicPerm)
    (six_swap (K := K)) hcc
  have cases_perm : ∀ e : Equiv.Perm (Fin 3),
      e = Equiv.refl _ ∨ e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm ∨
      e = swapFirstTwoPerm ∨ e = swapFirstTwoPerm.trans cyclicPerm ∨
      e = swapFirstTwoPerm.trans (cyclicPerm.trans cyclicPerm) := by decide
  rcases cases_perm sigma with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [perm_refl_eq]
    exact Isomorphic.refl _
  · exact six_cycle T
  · exact hcc T
  · exact six_swap T
  · exact hsc T
  · exact hscc T


#print axioms solution
