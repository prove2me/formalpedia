-- Prove2me | Theorems.Thm_lean_workbook_plus_53571
-- name    : lean_workbook_plus_53571
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/c0067c73-21ed-4d33-99e3-f8832ed129f7
-- statement:
--   Let $m$ and $n$ be natural numbers such that the number $mn + m + n\equiv 4 \pmod{6}.$ Show that $mn$ is divisible by $12$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53571 (m n : ℕ) : (m * n + m + n) % 6 = 4 → 12 ∣ m * n   :=  by sorry
