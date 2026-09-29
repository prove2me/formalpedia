-- Prove2me | Theorems.Thm_lean_workbook_plus_37819
-- name    : lean_workbook_plus_37819
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/23de84e4-7d77-4bfb-9e0a-768993d93dd5
-- statement:
--   Prove: $ \sin (\frac {\pi}{2m}) \sin (\frac {2\pi}{2m}) \sin (\frac {3\pi}{2m})\dots \sin (\frac {(m - 1)\pi}{2m}) = \frac {\sqrt {m}}{2^{m - 1}}$ $ \sin (\frac {\pi}{4m}) \sin (\frac {3\pi}{4m}) \sin (\frac {5\pi}{4m})\dots \sin (\frac {(2m - 1)\pi}{4m}) = \frac {\sqrt {2}}{2^{m - 1}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37819 : ∀ m : ℕ, (∏ k in Finset.Icc 1 (m - 1), sin ((k * π) / (2 * m))) = √m / 2 ^ (m - 1) ∧ (∏ k in Finset.Icc 1 (2 * m - 1), sin ((k * π) / (4 * m))) = √2 / 2 ^ (m - 1)   :=  by sorry
