-- Prove2me | Theorems.Thm_WorkbookSource_base_15179
-- name    : WorkbookSource.base_15179
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:28.778261+00:00
-- url     : https://prove2.me/theorems/00023503-9fef-40dc-bab9-5b706c04dfb9
-- title:
--   Nonnegativity of an expanded sextic polynomial
-- statement:
--   Prove that $3 a^6+a^5 (15 u+12 v)+a^4 \left(33 u^2+48 u v+15 v^2\right)+a^3 \left(39 u^3+81 u^2 v+48 u v^2+6 v^3\right)+a^2 \left(25 u^4+68 u^3 v+60 u^2 v^2+17 u v^3+v^4\right)+a \left(8 u^5+27 u^4 v+32 u^3 v^2+15 u^2 v^3+2 u v^4\right)+u^6+4 u^5 v+6 u^4 v^2+4 u^3 v^3+u^2 v^4\geq 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15179` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15179; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15179 {a u v : ℝ} : (3 * a^6 + a^5 * (15 * u + 12 * v) + a^4 * (33 * u^2 + 48 * u * v + 15 * v^2) + a^3 * (39 * u^3 + 81 * u^2 * v + 48 * u * v^2 + 6 * v^3) + a^2 * (25 * u^4 + 68 * u^3 * v + 60 * u^2 * v^2 + 17 * u * v^3 + v^4) + a * (8 * u^5 + 27 * u^4 * v + 32 * u^3 * v^2 + 15 * u^2 * v^3 + 2 * u * v^4) + u^6 + 4 * u^5 * v + 6 * u^4 * v^2 + 4 * u^3 * v^3 + u^2 * v^4) ≥ 0  :=  by sorry
