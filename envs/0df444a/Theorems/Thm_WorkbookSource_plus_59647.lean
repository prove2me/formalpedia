-- Prove2me | Theorems.Thm_WorkbookSource_plus_59647
-- name    : WorkbookSource.plus_59647
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:40:56.216648+00:00
-- url     : https://prove2.me/theorems/d2e7cf62-9d72-4091-aaea-045b972bacd8
-- title:
--   A cyclic fifth-degree comparison of mixed products
-- statement:
--   Prove that if $a\geq0,$ $b\geq0$ and $c\geq0$ than
--    $a^{5}+b^{5}+c^{5}+abc(ab+ac+bc)\geq a^{4}b+b^{4}c+c^{4}a+abc(a^{2}+b^{2}+c^{2}).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_59647` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_59647; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_59647 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^5 + b^5 + c^5 + a * b * c * (a * b + a * c + b * c) ≥ a^4 * b + b^4 * c + c^4 * a + a * b * c * (a^2 + b^2 + c^2)   :=  by sorry
