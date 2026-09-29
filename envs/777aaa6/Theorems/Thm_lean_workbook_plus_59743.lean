-- Prove2me | Theorems.Thm_lean_workbook_plus_59743
-- name    : lean_workbook_plus_59743
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/458e415f-7ecc-4489-96f2-a000fde66693
-- statement:
--   Solution by Binomial Identities $\dbinom{n}{0}+\dbinom{n+1}{1}+....+\dbinom{n+k}{k}$ $=\dbinom{n+1}{0}+\dbinom{n+1}{1}+....+\dbinom{n+k}{k}$ $=\dbinom{n+2}{1}+\dbinom{n+2}{2}+....+\dbinom{n+k}{k}$ $\vdots$ $\vdots$ $=\dbinom{n+k}{k-1}+\dbinom{n+k}{k}$ $=\boxed{\dbinom{n+k+1}{k}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59743 (n k : ℕ) :
  ∑ i in (Finset.range (k + 1)), (n + i).choose i = (n + k + 1).choose k   :=  by sorry
