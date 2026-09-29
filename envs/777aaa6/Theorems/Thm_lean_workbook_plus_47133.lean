-- Prove2me | Theorems.Thm_lean_workbook_plus_47133
-- name    : lean_workbook_plus_47133
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ddea6cf3-a3dd-402f-860f-02bf386948a1
-- statement:
--   Let $ 0\leq x,y,z<p $ then $ y\equiv bx(mod p) $ and $ z\equiv cy(mod p)\implies z\equiv bcx(mod p) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47133 (p : ℕ) (b c x y z : ℤ) (hp : 0 < p) (h : 0 ≤ x ∧ 0 ≤ y ∧ 0 ≤ z) (h2 : x < p ∧ y < p ∧ z < p) (h3 : y ≡ b * x [ZMOD p]) (h4 : z ≡ c * y [ZMOD p]) : z ≡ b * c * x [ZMOD p]   :=  by sorry
