-- Prove2me | Theorems.Thm_lean_workbook_plus_50222
-- name    : lean_workbook_plus_50222
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/ef0bacdb-81f2-4f67-921e-8178f17bb9f7
-- statement:
--   It follows that $ 3^c \equiv 8 \pmod{19}$ and since order of $ 3$ mod $ 19$ is $ 18$ this implies that $ c \equiv 3 \pmod{18}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50222  (c : ℕ)
  (h₀ : 0 < c)
  (h₁ : (3^c) % 19 = 8) :
  (c % 18) = 3   :=  by sorry
