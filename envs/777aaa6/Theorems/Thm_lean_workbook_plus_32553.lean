-- Prove2me | Theorems.Thm_lean_workbook_plus_32553
-- name    : lean_workbook_plus_32553
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f43bc2ed-0154-402b-90c3-ccaec2184c1d
-- statement:
--   Show that $a\equiv{b}\pmod{m}$ and $0<a<m$ and $0<b<m$ imply $a=b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32553 (a b m : ℕ) (ha : 0 < a ∧ a < m) (hb : 0 < b ∧ b < m) (hab : a ≡ b [ZMOD m]) : a = b   :=  by sorry
