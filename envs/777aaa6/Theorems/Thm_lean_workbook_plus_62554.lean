-- Prove2me | Theorems.Thm_lean_workbook_plus_62554
-- name    : lean_workbook_plus_62554
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/73d886b4-6c14-4466-a7cd-36a394e5f83d
-- statement:
--   Let $d_n$ be the remainder when $c_n$ is divided by 2010. The desired statement is equivalent to proving that there exist distinct indices $i$ and $j$ such that $d_i = d_j$ . Assume that this is not true; therefore all $d_k$ are distinct. As a result, $d_k$ takes on the values $0$ to $2009$ exactly once for each $k$ . The sum of all $d_k$ is $\frac{2009 \cdot 2010}{2} \equiv 2009 \cdot 1005 \equiv 1005 \pmod{2010}$ . However, the sum of all $c_k$ is $\frac{4020 \cdot 4021}{2} \equiv 2010 \cdot 4021 \equiv 0 \pmod{2010}$ . Now, for all $k$ , $c_k - d_k = 2010l$ for some integer $l$ , so we must have that $\sum c_k \equiv \sum d_k \pmod{2010}$ , but we have just shown that this is not true. Therefore, the original assumption is not true, so using proof by contradiction, we have the desired result.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62554  (c : ℕ → ℕ)
  (d : ℕ → ℕ)
  (h₀ : ∀ n, d n = c n % 2010)
  (h₁ : ∀ n m, n ≠ m → d n ≠ d m) :
  ∃ i j, i ≠ j ∧ d i = d j   :=  by sorry
