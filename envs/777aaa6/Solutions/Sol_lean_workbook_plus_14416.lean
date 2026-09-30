-- Prove2me | solution 1 for lean_workbook_plus_14416
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:42:53.79975+00:00
-- url     : https://prove2.me/submissions/db0896a7-18ae-4c72-9243-7b0a3dcbe4e9

import Mathlib.Analysis.Complex.Basic

theorem solution {A B : Type} (s : A → B) : (∀ b : B, ∃ a : A, b = s a) ↔ Function.Surjective s := by
  constructor
  · intro h b
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, ha.symm⟩
  · intro h b
    obtain ⟨a, ha⟩ := h b
    exact ⟨a, ha.symm⟩
