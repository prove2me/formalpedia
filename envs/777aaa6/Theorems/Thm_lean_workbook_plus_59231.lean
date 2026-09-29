-- Prove2me | Theorems.Thm_lean_workbook_plus_59231
-- name    : lean_workbook_plus_59231
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/95843f7a-3690-4843-8f4b-4d2fde281ec3
-- statement:
--   If $ d$ divides $ n$ , then so does $ \frac{n}{d}$ . And $ \frac{n}{d}$ is going to be less than $ \sqrt{n}$ if and only if $ d$ is greater than $ \sqrt{n}$ . What you meant is $ \text{min} \left( d, \frac{n}{d} \right) \le \lfloor \sqrt{n} \rfloor$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59231 (n : ℕ) : ∀ d ∈ divisors n, min d (n/d) ≤ n   :=  by sorry
