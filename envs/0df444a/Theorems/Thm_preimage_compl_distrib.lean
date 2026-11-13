-- Prove2me | Theorems.Thm_preimage_compl_distrib
-- name    : preimage_compl_distrib
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:51:23.664207+00:00
-- url     : https://prove2.me/theorems/0c7c8669-bed0-4745-8dd2-82dee7309780
-- title:
--   04_thm_4_2: preimage_compl_distrib
-- statement:
--   Original source theorem `preimage_compl_distrib` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_2.lean

import Mathlib.Data.Set.Lattice
open Set
universe u v w
variable {Ω : Type u} {Ω' : Type v} {Ω'' : Type w} {I : Type _}
variable (f : Ω → Ω') (g : Ω' → Ω'') (A : Set Ω') (Ai : I → Set Ω') (B : Set Ω'')

theorem preimage_compl_distrib : f ⁻¹' (Aᶜ) = (f ⁻¹' A)ᶜ := by
  sorry
