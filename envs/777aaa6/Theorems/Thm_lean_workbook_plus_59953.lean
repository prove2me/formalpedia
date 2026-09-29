-- Prove2me | Theorems.Thm_lean_workbook_plus_59953
-- name    : lean_workbook_plus_59953
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/ea0e07c2-f7e1-4299-b5db-7e0e720887de
-- statement:
--   Let $a,b \in \mathbb{Z}$ and $m,n \in \mathbb{N}$ . Show that if $a \equiv b (mod n)$ and if $m|n$ , then $a \equiv b (mod m)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59953 (a b : ℤ) (m n : ℕ) (h1 : a ≡ b [ZMOD n]) (h2 : m ∣ n) : a ≡ b [ZMOD m]   :=  by sorry
