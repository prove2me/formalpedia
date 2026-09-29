-- Prove2me | solution 1 for mme_released_global_profile_count_identities
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T11:27:48.30861+00:00
-- url     : https://prove2.me/submissions/29cc1975-505a-484d-acda-9e91e1a097bd

import Definitions.Def_mme_released_global_profile_data
import Theorems.Thm_mme_released_global_joint_counts_valid
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem list_hist_mass {A W : Type*} [Fintype W] [DecidableEq W] (f : A → W) (l : List (A × ℕ)) :
    (∑ w, (l.map (fun a ↦ if f a.1 = w then a.2 else 0)).sum) =
      (l.map Prod.snd).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,Finset.sum_add_distrib,ih]
    simp

private theorem list_hist_pos {A W : Type*} [DecidableEq W] (f : A → W)
    (l : List (A × ℕ)) (w : W)
    (h : 0 < (l.map (fun a ↦ if f a.1 = w then a.2 else 0)).sum) :
    ∃ a ∈ l, f a.1 = w ∧ 0 < a.2 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases heq : f a.1 = w
    · by_cases ha : 0 < a.2
      · exact ⟨a,by simp,heq,ha⟩
      · have hh : 0 < (l.map (fun a ↦ if f a.1 = w then a.2 else 0)).sum := by
          simpa [heq,Nat.eq_zero_of_not_pos ha] using h
        obtain ⟨b,hb,hb'⟩ := ih hh
        exact ⟨b,by simp [hb],hb'⟩
    · have hh : 0 < (l.map (fun a ↦ if f a.1 = w then a.2 else 0)).sum := by
        simpa [heq] using h
      obtain ⟨b,hb,hb'⟩ := ih hh
      exact ⟨b,by simp [hb],hb'⟩

private theorem atom_supported (a : Fin 1296) : ∀ r,
    (atom a 0 r).val + (atom a 1 r).val + (atom a 2 r).val = 2 := by
  intro r
  have h : ∀ j : Fin 6, (elementary j 0).val + (elementary j 1).val +
      (elementary j 2).val = 2 := by decide
  exact h _

attribute [local irreducible] jointRows alpha atom

theorem solution (owner : Fin 6) :
    (∑ c : Shape, coarseCounts owner c) = denominator^5 ∧
    (∀ c : Shape, ∑ v : JointWord, jointCounts owner c v = coarseCounts owner c) ∧
    (∀ c v, 0 < jointCounts owner c v →
      (∀ i, CWCells.grade (v i) = (c.val i).val) ∧
      ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) ∧
    (∀ i c, ∑ w : Word, wordCounts owner i c w = coarseCounts owner c) := by
  have hv := mme_released_global_joint_counts_valid
  have hm : ∀ c : Shape, ∑ v : JointWord, jointCounts owner c v = coarseCounts owner c := by
    intro c
    unfold jointCounts coarseCounts rowCounts
    rw [← Finset.mul_sum]
    apply congrArg (fun n ↦ alpha owner (shapeEquiv.symm c) * n)
    exact (list_hist_mass atom (jointRows owner (shapeEquiv.symm c))).trans
      (hv.2.1 owner (shapeEquiv.symm c)).1
  refine ⟨?_,hm,?_,?_⟩
  · rw [← Equiv.sum_comp shapeEquiv]
    simp only [coarseCounts,Equiv.symm_apply_apply]
    rw [← Finset.sum_mul,hv.1 owner]
    ring
  · intro c v h
    have hp : 0 < rowCounts owner (shapeEquiv.symm c) v := by
      have hh := Nat.pos_of_mul_pos_left h
      exact hh
    obtain ⟨a,ha,hav,han⟩ := list_hist_pos atom (jointRows owner (shapeEquiv.symm c)) v hp
    subst v
    refine ⟨?_,atom_supported a.1⟩
    intro i
    have hg := (hv.2.1 owner (shapeEquiv.symm c)).2 a ha i
    simpa only [show shape (shapeEquiv.symm c) = c from shapeEquiv.apply_symm_apply c] using hg
  · intro i c
    unfold wordCounts
    rw [Finset.sum_comm]
    simpa using hm c
