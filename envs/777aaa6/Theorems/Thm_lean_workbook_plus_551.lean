-- Prove2me | Theorems.Thm_lean_workbook_plus_551
-- name    : lean_workbook_plus_551
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a88a3c36-3e4b-4b2f-9823-74fa75b022a7
-- statement:
--   Then $\mathcal{S}=\{(2,2),(2,3),(2,401),(3,2),(3,3),(3,7),(3,127),(7,2),(7,3),(7,7),(7,827),(7,10529),(19,3),(29,7),(4733,7)\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_551 {s : ℕ × ℕ | s.1 ∈ ({2,3,7,19,29,4733} : Finset ℕ) ∧ s.2 ∈ ({2,3,7,19,29,4733} : Finset ℕ) ∧ s.1 ≠ s.2}  = {⟨2,2⟩,⟨2,3⟩,⟨2,401⟩,⟨3,2⟩,⟨3,3⟩,⟨3,7⟩,⟨3,127⟩,⟨7,2⟩,⟨7,3⟩,⟨7,7⟩,⟨7,827⟩,⟨7,10529⟩,⟨19,3⟩,⟨29,7⟩,⟨4733,7⟩}   :=  by sorry
