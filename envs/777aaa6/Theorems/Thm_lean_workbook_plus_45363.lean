-- Prove2me | Theorems.Thm_lean_workbook_plus_45363
-- name    : lean_workbook_plus_45363
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/f644a52b-768a-4730-bf89-7dbe194172e3
-- statement:
--   If the GCD of $a$ and $b$ is $12$ and the LCM of $a$ and $b$ is $168$ , what is the value of $a\times b$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45363 (a b : ℕ) (hgcd : Nat.gcd a b = 12) (hlcm : Nat.lcm a b = 168) : a * b = 2016   :=  by sorry
