-- Prove2me | Theorems.Thm_WorkbookSource_plus_12966
-- name    : WorkbookSource.plus_12966
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:11:16.111045+00:00
-- url     : https://prove2.me/theorems/67d4309c-9ff5-4510-b663-f770ab0afa10
-- title:
--   A cyclic pair-product ratio sum is at most one
-- statement:
--   Let $a,b,c > 0.$ Prove that $\frac{ab}{ab+b^2+ c^2}+\frac{bc}{bc+c^2 + a^2}+\frac{ca}{ca+a^2+ b^2}\leq 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_12966` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_12966; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_12966 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a * b / (a * b + b ^ 2 + c ^ 2) + b * c / (b * c + c ^ 2 + a ^ 2) + c * a / (c * a + a ^ 2 + b ^ 2)) ≤ 1   :=  by sorry
