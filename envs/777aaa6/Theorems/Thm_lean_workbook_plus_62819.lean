-- Prove2me | Theorems.Thm_lean_workbook_plus_62819
-- name    : lean_workbook_plus_62819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/6d00d61f-214c-4d84-a7b4-9a0954633a08
-- statement:
--   Prove that if $n=p^2$ , then $d=p$ , which means $d - 1 \mid n - 1$ (i.e. $p - 1 \mid p^2 - 1$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62819 (n : ℕ) (p : ℕ) (hp : p.Prime) (h : n = p^2) (d : ℕ) (hd : d = p) : d - 1 ∣ n - 1   :=  by sorry
