-- Prove2me | Theorems.Thm_lean_workbook_plus_63532
-- name    : lean_workbook_plus_63532
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/f85978b6-c038-4e04-8c49-0b9eb52eb0c8
-- statement:
--   Let $(u_n)$ be a sequence that : $u_1=1; u_2=12; u_{n+1}=\dfrac{(u_n+5)^2}{u_{n-1}}$. Prove that: i) $u_n \in \mathbb{Z}^+, \forall n \in \mathbb{Z}. $ ii) $\sqrt{u_{2015}}+\sqrt{3u_{2016}} \in \mathbb{Z}^+$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63532 (u : ℕ → ℚ) (u1 : u 0 = 1) (u2 : u 1 = 12) (u_rec : ∀ n, u (n + 1) = (u n + 5) ^ 2 / u (n - 1)) : ∀ n, 0 < n → (u n).den = 1 ∧ (u n).num > 0   :=  by sorry
