-- Prove2me | Theorems.Thm_preimage_comp_distrib
-- name    : preimage_comp_distrib
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:51:45.829208+00:00
-- url     : https://prove2.me/theorems/01204d00-0b8b-4a59-b011-6c61a90d0cd0
-- title:
--   04_thm_4_2: preimage_comp_distrib
-- statement:
--   Original source theorem `preimage_comp_distrib` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_2.lean

import Mathlib.Data.Set.Lattice
open Set
universe u v w
variable {Ω : Type u} {Ω' : Type v} {Ω'' : Type w} {I : Type _}
variable (f : Ω → Ω') (g : Ω' → Ω'') (A : Set Ω') (Ai : I → Set Ω') (B : Set Ω'')

theorem preimage_comp_distrib (h : Ω → Ω'') (hw : h = g ∘ f) :
    h ⁻¹' B = f ⁻¹' (g ⁻¹' B) := by
  sorry
