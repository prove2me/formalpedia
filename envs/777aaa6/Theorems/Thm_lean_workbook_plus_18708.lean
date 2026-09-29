-- Prove2me | Theorems.Thm_lean_workbook_plus_18708
-- name    : lean_workbook_plus_18708
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/e0644d43-7a3a-4c34-b1c9-fb0064afdcd1
-- statement:
--   Prove that, for any ${ n \in \mathbb N}$ , \n $ \left\lfloor{n \over 3}\right\rfloor+\left\lfloor{n+2 \over 6}\right\rfloor+\left\lfloor{n+4 \over 6}\right\rfloor=\left\lfloor{n \over 2}\right\rfloor+\left\lfloor{n+3 \over 6}\right\rfloor. $\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18708 : ∀ n : ℕ, (Nat.floor (n / 3) + Nat.floor ((n + 2) / 6) + Nat.floor ((n + 4) / 6) = Nat.floor (n / 2) + Nat.floor ((n + 3) / 6))   :=  by sorry
