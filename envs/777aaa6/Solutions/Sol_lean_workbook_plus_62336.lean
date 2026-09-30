-- Prove2me | solution 1 for lean_workbook_plus_62336
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:17:45.864915+00:00
-- url     : https://prove2.me/submissions/95f10660-a4a9-4e92-bcdf-bd17fd721266

import Mathlib.Analysis.Complex.Basic

theorem solution {n : ℕ} (p e : Fin n → ℝ) (hp : ∑ i, p i = 1) : ∃ k, ∑ i, p i * e i = k :=
  ⟨_, rfl⟩
