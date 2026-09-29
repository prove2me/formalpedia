-- Prove2me | Theorems.Thm_lean_workbook_plus_51761
-- name    : lean_workbook_plus_51761
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/fd667cd0-6a7e-4473-b4e6-4b1c3624b38d
-- statement:
--   To answer Pocket Sand's question, we use prime factorization for $576$ . Since $576=2^6\cdot 3^2$ , we have $(1+6)(1+2)=21$ positive divisors.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51761 :
  (∑ k in (Nat.divisors 576), 1) = 21   :=  by sorry
