-- Prove2me | solution 1 for ForkPinning.mutualInfo_const_left
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T05:23:44.810125+00:00
-- url     : https://prove2.me/submissions/788f05e6-ebbb-4488-8cc8-f8ceedabd382

import Mathlib
import Definitions.Def_Probability_ForkPinningCore
open ForkPinning Finset Real in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] {κ β : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype β] [DecidableEq β] (c : κ) (Y : Ω → β) : mutualInfo (fun _ => c) Y = 0 := by
  classical
  have hcard : (0 : ℝ) < Fintype.card Ω := by
    have := Fintype.card_pos (α := Ω)
    exact_mod_cast this
  have hprb : ∀ k : κ, prb (fun _ : Ω => c) k = if k = c then 1 else 0 := by
    intro k
    unfold prb fiber
    by_cases hk : k = c
    · rw [if_pos hk, hk]
      have e : (Finset.univ.filter (fun _ : Ω => c = c)) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro _ _
        rfl
      rw [e, Finset.card_univ]
      field_simp
    · have e : (Finset.univ.filter (fun _ : Ω => c = k)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro _ _ h
        exact hk h.symm
      rw [e, if_neg hk]
      simp
  have hHX : H (fun _ : Ω => c) = 0 := by
    unfold H
    have e : ∀ k : κ, negMulLog (prb (fun _ : Ω => c) k) = 0 := by
      intro k
      rw [hprb k]
      by_cases hk : k = c <;> simp [hk, Real.negMulLog]
    rw [Finset.sum_congr rfl (fun k _ => e k)]
    simp
  have hjprb : ∀ (k : κ) (b : β), prb (joint (fun _ : Ω => c) Y) (k, b)
      = if k = c then prb Y b else 0 := by
    intro k b
    unfold prb joint fiber
    by_cases hk : k = c
    · rw [if_pos hk, hk]
      have e : (Finset.univ.filter (fun ω : Ω => (c, Y ω) = (c, b)))
          = Finset.univ.filter (fun ω : Ω => Y ω = b) := by
        apply Finset.filter_congr
        intro ω _
        simp [Prod.ext_iff]
      rw [e]
    · have e : (Finset.univ.filter (fun ω : Ω => (c, Y ω) = (k, b))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ω _ h
        exact hk (congrArg Prod.fst h).symm
      rw [e, if_neg hk]
      simp
  have hHJ : H (joint (fun _ : Ω => c) Y) = H Y := by
    unfold H
    rw [Fintype.sum_prod_type]
    have e : ∀ k : κ, ∑ b : β, negMulLog (prb (joint (fun _ : Ω => c) Y) (k, b))
        = if k = c then ∑ b : β, negMulLog (prb Y b) else 0 := by
      intro k
      by_cases hk : k = c
      · rw [if_pos hk]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [hjprb k b, if_pos hk]
      · rw [if_neg hk]
        have e2 : ∀ b : β, negMulLog (prb (joint (fun _ : Ω => c) Y) (k, b)) = 0 := by
          intro b
          rw [hjprb k b, if_neg hk]
          simp [Real.negMulLog]
        rw [Finset.sum_congr rfl (fun b _ => e2 b)]
        simp
    rw [Finset.sum_congr rfl (fun k _ => e k),
      Finset.sum_ite_eq' Finset.univ c (fun _ => ∑ b : β, negMulLog (prb Y b)), if_pos (Finset.mem_univ c)]
  unfold mutualInfo
  rw [hHX, hHJ]
  ring
