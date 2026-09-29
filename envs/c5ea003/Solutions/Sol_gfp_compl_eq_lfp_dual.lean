-- Prove2me | solution 1 for gfp_compl_eq_lfp_dual
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:08:15.05404+00:00
-- url     : https://prove2.me/submissions/5a42d565-32f3-43c9-a624-ff97f3ba390b

import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalStoneSemiringBridge

open Set

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem solution (F : Set σ → Set σ) (hF : Monotone F) :
    (gfpSet F)ᶜ = sInf {X : Set σ | dualOp F X ⊆ X} := by
  simp only [gfpSet, dualOp, sSup_eq_sUnion, sInf_eq_sInter]
  ext x
  simp only [mem_compl_iff, mem_sUnion, mem_sInter, mem_setOf_eq]
  constructor
  · intro hx Y hY
    have hpostfix : Yᶜ ⊆ F Yᶜ := by
      intro y hy
      have : y ∉ (F Yᶜ)ᶜ := fun hc => hy (hY hc)
      simpa using this
    exact not_not.mp fun hxc => hx ⟨Yᶜ, hpostfix, hxc⟩
  · intro hx ⟨t, ht, hxt⟩
    have hY : dualOp F (tᶜ) ⊆ tᶜ := by
      intro y hy
      have : y ∉ F t := by
        simp only [dualOp, mem_compl_iff, compl_compl] at hy
        exact hy
      exact fun hyt => this (ht hyt)
    exact (hx (tᶜ) hY) hxt
