-- Prove2me | Theorems.Thm_lean_workbook_plus_74009
-- name    : lean_workbook_plus_74009
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/cd0f7611-2801-4b2d-8947-dac133bd210d
-- statement:
--   Let $m \in Z^+$ which satisfy: $ a^4 \vdots m \Rightarrow a \vdots m, \forall a \in Z^+ $. Prove that: $ a^5 \vdots m \Rightarrow a \vdots m, \forall a \in Z^+ $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74009 {m : ℕ} (hm : 0 < m) (h5 : ∀ a : ℕ, 0 < a → a^4 ∣ m → a ∣ m) : ∀ a : ℕ, 0 < a → a^5 ∣ m → a ∣ m   :=  by sorry
