-- Prove2me | Theorems.Thm_mme_dwz_component_disallowed_word_mismatches_profile
-- name    : mme_dwz_component_disallowed_word_mismatches_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T10:06:22.713857+00:00
-- url     : https://prove2.me/theorems/b5328566-e65b-420b-9c1c-a2d9e9fc00fe
-- title:
--   A disallowed component word mismatches every word with the prescribed profile
-- statement:
--   Let a source component word be decoded letterwise into three grades. If its left-grade histogram is not the prescribed Table-2 split for row s at scale m, while a target word has exactly that prescribed histogram, then the decoded source word and the target word disagree at some position. This is the finite profile mismatch that forces every disallowed source basis word to vanish under a selected balanced address projector.
-- source:
--   R. Duan, H. Wu, and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, Definitions 5.3-5.4 and the exact component split constraints.

import Mathlib.Tactic
import Definitions.Def_mme_dwz_component_word_projection

open MME MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_component_disallowed_word_mismatches_profile
    {n : ℕ} (s : Fin 15) (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6 1) n)
    (hnot : ¬ ∀ a : Fin 3,
      Fintype.card {r : Fin n //
        (PowIndex.get n w r).leftGrade = a} =
          MME.DWZTable2Counts.split s a * m)
    (target : Fin n → Fin 3)
    (htarget : ∀ a : Fin 3,
      Fintype.card {r : Fin n // target r = a} =
        MME.DWZTable2Counts.split s a * m)
    (labelGrade : LiftedCoarsePair.{u} 6 1 → Fin 3)
    (htranslate : ∀ p, p.leftGrade = labelGrade p) :
    ∃ r : Fin n,
      labelGrade (PowIndex.get n w r) ≠ target r := by
  sorry
