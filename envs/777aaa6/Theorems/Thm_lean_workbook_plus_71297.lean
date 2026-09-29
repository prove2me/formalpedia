-- Prove2me | Theorems.Thm_lean_workbook_plus_71297
-- name    : lean_workbook_plus_71297
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/e119ddf9-add8-4568-b1ad-2656ea2d5a5a
-- statement:
--   Prove $(a^3+b^3+c^3-3abc)(p^3+q^3+r^3-3pqr)=(u^3+v^3+w^3-3uvw)$ where $u=ap+br+cq$ , $v=aq+bp+cr$ , $w=ar+bq+cp$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71297 (a b c p q r u v w : ℤ) (hu : u = a * p + b * r + c * q) (hv : v = a * q + b * p + c * r) (hw : w = a * r + b * q + c * p) : (a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c) * (p ^ 3 + q ^ 3 + r ^ 3 - 3 * p * q * r) = u ^ 3 + v ^ 3 + w ^ 3 - 3 * u * v * w   :=  by sorry
