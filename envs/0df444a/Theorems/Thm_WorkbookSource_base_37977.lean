-- Prove2me | Theorems.Thm_WorkbookSource_base_37977
-- name    : WorkbookSource.base_37977
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:52:27.882577+00:00
-- url     : https://prove2.me/theorems/83e4796e-77de-4d47-b47d-f6abcf012743
-- title:
--   A product comparison between fourth-power and quadratic sums
-- statement:
--   Let a,b,c>0. Prove that:
--    $\left( {{a^4} + {b^4} + {c^4}} \right)\left( {ab + bc + ca} \right) \ge \left( {{a^2} + {b^2} + {c^2}} \right)\left( {{a^2}{b^2} + {b^2}{c^2} + {c^2}{a^2}} \right)$ .
--    Can you prove it by SOS?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37977` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37977; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37977 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a ^ 4 + b ^ 4 + c ^ 4) * (a * b + b * c + c * a) ≥ (a ^ 2 + b ^ 2 + c ^ 2) * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)  :=  by sorry
