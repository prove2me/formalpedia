-- Prove2me | Theorems.Thm_lean_workbook_plus_37880
-- name    : lean_workbook_plus_37880
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/625ae212-89b4-4334-8064-24b76db99858
-- statement:
--   Let $ A = \{ 1, 2, \cdots , 12 \} $ . Find the number of one-to-one function $ f :A \to A $ satisfying following condition: for all $ i \in A $ , $ f(i)-i $ is not a multiple of $ 3 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37880 (A: Finset ℕ) (hA: A = Finset.Icc 1 12): ∃ f : ℕ → ℕ, Function.Injective f ∧ ∀ i ∈ A, ¬ 3 ∣ (f i - i)   :=  by sorry
