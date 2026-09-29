-- Prove2me | solution 1 for mme_dwz_component_disallowed_word_mismatches_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:06:31.876102+00:00
-- url     : https://prove2.me/submissions/ab0f1a2e-75bc-4d86-bcb6-38a0106b4d9d

import Mathlib.Tactic
import Definitions.Def_mme_dwz_component_word_projection

open MME MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem solution
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
  by_contra hnone
  push_neg at hnone
  apply hnot
  intro a
  have hprop (r : Fin n) :
      (PowIndex.get n w r).leftGrade = a ↔ target r = a := by
    rw [htranslate]
    rw [hnone r]
  calc
    Fintype.card {r : Fin n //
        (PowIndex.get n w r).leftGrade = a} =
        Fintype.card {r : Fin n // target r = a} := by
          exact Fintype.card_congr
            ((Equiv.refl (Fin n)).subtypeEquiv hprop)
    _ = MME.DWZTable2Counts.split s a * m := htarget a
