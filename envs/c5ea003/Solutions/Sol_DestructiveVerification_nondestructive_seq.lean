-- Prove2me | solution 1 for DestructiveVerification.nondestructive_seq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T20:56:37.472235+00:00
-- url     : https://prove2.me/submissions/b5d5c559-7616-4934-a83b-5f86e65488a1

import Mathlib
import Definitions.Def_Combinatorics_DestructiveVerification
open DestructiveVerification in
theorem solution {D : Type*} {t₁ t₂ : Test D} (h₁ : Nondestructive t₁) (h₂ : Nondestructive t₂) :
    Nondestructive (seq t₁ t₂) := by
  -- running `t₁` then `t₂` leaves the dish as it was
  intro d
  show residue t₂ (residue t₁ d) = d
  rw [h₁ d, h₂ d]
