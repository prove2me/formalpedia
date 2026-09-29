-- Prove2me | solution 1 for Talagrand.dTsq_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:35:49.974052+00:00
-- url     : https://prove2.me/submissions/eeeace29-82df-4fc6-8102-6fda177b442b

import Mathlib
import Definitions.Def_Probability_TalagrandDefs
import Definitions.Def_Probability_TalagrandHypercube
open Talagrand Finset Real in
theorem solution {α : Type*} [DecidableEq α] {n : ℕ} (y x : Fin n → α) :
    dTsq {y} x = ∑ i, hamm (x i) (y i) ^ 2 := by
  unfold dTsq
  have hset : {s : ℝ | ∃ v, IsRep {y} x v ∧ s = sqn v}
      = {∑ i, hamm (x i) (y i) ^ 2} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨⟨fun i => hamm (x i) (y i), ⟨1, fun _ => 1, fun _ => y, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
    · intro j
      norm_num
    · simp
    · intro j
      simp
    · intro i
      simp
    · unfold sqn
      rfl
    · intro s hs
      obtain ⟨v, ⟨k, w, ys, hw0, hw1, hmem, hv⟩, rfl⟩ := hs
      have hys : ∀ j, ys j = y := by
        intro j
        have := hmem j
        simpa using this
      have hvi : ∀ i, v i = hamm (x i) (y i) := by
        intro i
        rw [hv i]
        have e : ∀ j, w j * hamm (x i) (ys j i) = w j * hamm (x i) (y i) := by
          intro j
          rw [hys j]
        rw [Finset.sum_congr rfl (fun j _ => e j), ← Finset.sum_mul, hw1, one_mul]
      unfold sqn
      exact Finset.sum_congr rfl (fun i _ => by rw [hvi i])
  rw [hset, csInf_singleton]
