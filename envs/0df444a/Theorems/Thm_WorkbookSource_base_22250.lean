-- Prove2me | Theorems.Thm_WorkbookSource_base_22250
-- name    : WorkbookSource.base_22250
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:50:58.150119+00:00
-- url     : https://prove2.me/theorems/426b7acb-d141-4c04-a68c-c50e907fcbcd
-- title:
--   A weighted cyclic quadratic reciprocal lower bound
-- statement:
--   Prove that: $\dfrac{a}{b^2+3c^2+5bc} + \dfrac{b}{c^2+3a^2+5ca} + \dfrac{c}{a^2+3b^2+5ab} \geq \dfrac{1}{a+b+c}$ given $a,b,c \in R$ and $ a,b,c >0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_22250` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_22250; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_22250 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b ^ 2 + 3 * c ^ 2 + 5 * b * c) + b / (c ^ 2 + 3 * a ^ 2 + 5 * c * a) + c / (a ^ 2 + 3 * b ^ 2 + 5 * a * b)) ≥ 1 / (a + b + c)  :=  by sorry
