-- Prove2me | Theorems.Thm_lean_workbook_plus_17370
-- name    : lean_workbook_plus_17370
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/7fcf8421-22db-4da2-b779-5b58feacd9e9
-- statement:
--   Let $a_1$ , $a_2$ , $b_1$ , and $b_2$ be integers such that \n\begin{eqnarray*} a_1 \equiv a_2 \pmod{m} \\\n b_1 \equiv b_2 \pmod{m} \end{eqnarray*} \nShow that $a_1 + b_1 \equiv a_2 + b_2 \pmod{m}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17370 {a₁ a₂ b₁ b₂ m : ℤ} (ha : a₁ ≡ a₂ [ZMOD m]) (hb : b₁ ≡ b₂ [ZMOD m]) : a₁ + b₁ ≡ a₂ + b₂ [ZMOD m]   :=  by sorry
