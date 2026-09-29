-- Prove2me | Theorems.Thm_lean_workbook_plus_24740
-- name    : lean_workbook_plus_24740
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/5559d677-f0b9-4653-9e7c-f6969243fcc8
-- statement:
--   1. Let $r$ be the remainder when $a$ is divided by $m$ . Since $a\equiv b\pmod{m}$ , $r$ is also the remainder when $b$ is divided by $m$ . Thus, we have $r+c=r+c$ , so $a+c\equiv b+c\pmod{m}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24740 {a b c m : ℤ} (h₁ : a ≡ b [ZMOD m]) (h₂ : 0 < m) : (a + c) ≡ (b + c) [ZMOD m]   :=  by sorry
