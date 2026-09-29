-- Prove2me | Theorems.Thm_lean_workbook_plus_74924
-- name    : lean_workbook_plus_74924
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bcd98f42-3ae6-448f-ad9f-914ecd60d641
-- statement:
--   If $a,b$ be integers and $n,k$ be positive integers, such that $a\equiv b\pmod{n}$ , then $a^k\equiv b^k\pmod{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74924 {a b n : ℤ} (h : a ≡ b [ZMOD n]) (k : ℕ) : a ^ k ≡ b ^ k [ZMOD n]   :=  by sorry
