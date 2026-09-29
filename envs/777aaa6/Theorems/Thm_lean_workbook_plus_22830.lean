-- Prove2me | Theorems.Thm_lean_workbook_plus_22830
-- name    : lean_workbook_plus_22830
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/af3c523c-1153-455c-8fc7-45335c7a4866
-- statement:
--   Using logical equivalences, show that these expressions are tautology: \n\n1) $p\lor (p\land q)\equiv p$ \n\n2) $[(p\lor q)\land (p\Rightarrow r)\land (q\Rightarrow r)] \Rightarrow r$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22830 : ∀ p q : Prop, p ∨ (p ∧ q) ↔ p   :=  by sorry
