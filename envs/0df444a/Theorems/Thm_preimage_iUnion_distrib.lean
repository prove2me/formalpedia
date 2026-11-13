-- Prove2me | Theorems.Thm_preimage_iUnion_distrib
-- name    : preimage_iUnion_distrib
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:51:37.938423+00:00
-- url     : https://prove2.me/theorems/274e1a79-4f2b-4f9b-b6f4-998f9b8f4073
-- title:
--   04_thm_4_2: preimage_iUnion_distrib
-- statement:
--   Original source theorem `preimage_iUnion_distrib` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_2.lean

import Mathlib.Data.Set.Lattice
open Set
universe u v w
variable {Ω : Type u} {Ω' : Type v} {Ω'' : Type w} {I : Type _}
variable (f : Ω → Ω') (g : Ω' → Ω'') (A : Set Ω') (Ai : I → Set Ω') (B : Set Ω'')

theorem preimage_iUnion_distrib : f ⁻¹' (⋃ i, Ai i) = ⋃ i, f ⁻¹' (Ai i) := by
  sorry
