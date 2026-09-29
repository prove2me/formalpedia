-- Prove2me | Theorems.Thm_lean_workbook_plus_48042
-- name    : lean_workbook_plus_48042
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/1111a7ba-1078-4b5c-a4c3-d94edb579c75
-- statement:
--   Let's number the board from the top leftmost cell to the bottom rightmost cell with numbers from $0$ to $99$ . The number in cell $(x, y)$ will be equal to $10\cdot x + y$ . Each domino will now cover 3 squares that the sum of the numbers in them is divisible by $3$ . Since the sum of all the numbers is also divisible by $3$ , the number in the leftover cell must be divisible by $3$ . Now, each $90^\circ$ rotation with turn the number in cell $(x,y)$ from $10\cdot x + y$ to $10\cdot y + (9 - x)$ . If the cell $(x,y)$ is leftover in the first configuration, then it is still a leftover cell after the rotation. Thus, we have $3\mid 10\cdot x + y$ and $3\mid 10\cdot y + (9 - x)$ , or $3\mid x$ and $3\mid y$ . Since $0\le x, y\le 9$ , so $x,y\in\{0, 3, 6, 9\}$ . There are $16$ such pairs, account for $16$ cells.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48042  (x y : ℕ)
  (h₀ : 0 ≤ x ∧ x ≤ 9)
  (h₁ : 0 ≤ y ∧ y ≤ 9)
  (h₂ : 3 ∣ (10 * x + y))
  (h₃ : 3 ∣ (10 * y + (9 - x))) :
  x ∈ ({0, 3, 6, 9} : Finset ℕ) ∧ y ∈ ({0, 3, 6, 9} : Finset ℕ)   :=  by sorry
