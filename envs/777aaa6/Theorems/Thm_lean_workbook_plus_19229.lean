-- Prove2me | Theorems.Thm_lean_workbook_plus_19229
-- name    : lean_workbook_plus_19229
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/269f0449-d121-4c83-b0e8-c3b95653c804
-- statement:
--   The greatest common divisor of $n$ and $180$ is $12$ . The least common multiple of $n$ and $180$ is $720$ . Find $n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19229 (n : ℕ) (h1 : Nat.gcd n 180 = 12) (h2 : Nat.lcm n 180 = 720) : n = 48   :=  by sorry
