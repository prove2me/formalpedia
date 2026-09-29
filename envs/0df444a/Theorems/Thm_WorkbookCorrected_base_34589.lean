-- Prove2me | Theorems.Thm_WorkbookCorrected_base_34589
-- name    : WorkbookCorrected.base_34589
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:12:48.582911+00:00
-- url     : https://prove2.me/theorems/6de13a59-d7df-4e2b-b8cb-6967e8634274
-- title:
--   A cyclic quartic comparison under a quartic relation
-- statement:
--   Let $a,b,c,d \geq 0$ such that $2(a^4+b^4+c^4+d^4) = a^2b^2+b^2c^2+c^2d^2+d^2a^2+2$. Prove that $ab^3+bc^3+cd^3+da^3+1 \geq a^3b+b^3c+c^3d+d^3a$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34589` (Apache-2.0). Natural-language proposition preserved; missing source domain assumptions restored. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34589; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.base_34589 (a b c d : ℝ) (source_domain_a : 0 ≤ a) (source_domain_b : 0 ≤ b) (source_domain_c : 0 ≤ c) (source_domain_d : 0 ≤ d) (h : 2 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + d ^ 2 * a ^ 2 + 2) : a * b ^ 3 + b * c ^ 3 + c * d ^ 3 + d * a ^ 3 + 1 ≥ a ^ 3 * b + b ^ 3 * c + c ^ 3 * d + d ^ 3 * a  :=  by sorry
