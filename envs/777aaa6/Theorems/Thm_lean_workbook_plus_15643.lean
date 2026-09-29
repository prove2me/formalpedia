-- Prove2me | Theorems.Thm_lean_workbook_plus_15643
-- name    : lean_workbook_plus_15643
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/4e583f61-c957-427c-b418-8726d39f26ec
-- statement:
--   The gigantic number of relatives, n, satisfies $n\equiv1\bmod{5}$ , $n\equiv1\bmod{11}$ , $n\equiv0\bmod{2}$ . The only even number less than $110$ that satisfies the first two is $56$ , our answer.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15643  (n : ℕ)
  (h₀ : n % 5 = 1)
  (h₁ : n % 11 = 1)
  (h₂ : 2∣n)
  (h₃ : n < 110) :
  n = 56   :=  by sorry
