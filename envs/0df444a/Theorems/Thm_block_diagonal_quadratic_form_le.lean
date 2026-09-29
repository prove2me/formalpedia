-- Prove2me | Theorems.Thm_block_diagonal_quadratic_form_le
-- name    : block_diagonal_quadratic_form_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-25T02:33:19.492622+00:00
-- url     : https://prove2.me/theorems/abb8287d-2bd1-403d-b1c2-8132c9c1178d
-- statement:
--   **Block-diagonal quadratic-form bound.** For the block-diagonal matrix $V = \operatorname{blockdiag}(\operatorname{diag}(a), \operatorname{diag}(b))$ with $0 \le a_i \le B$ and $0 \le b_j \le B$, the quadratic form is dominated: $w^\top V w \le B\, w^\top w$ for all $w$. Combined with the eigenvalue-from-quadratic-form bridge, this gives $\lambda_{\max}(V) \le B$. This is the $V = \sum_c H_c^2 = \operatorname{blockdiag}(\operatorname{diag}(p^{-2}\,\text{rowEnergy}),\operatorname{diag}(p^{-2}\,\text{colEnergy}))$ step feeding the matrix-Khintchine engine with $B = (\text{sampled variance scale})^2$. Proof: split $w$ into its two blocks, the off-diagonal blocks are zero so the form splits into two diagonal quadratic forms, each bounded by the diagonal-entry bound.
-- source:
--   Standard linear algebra. This is exactly the V = ∑_c H_c² = blockdiag(diag(p⁻²rowEnergy) ⊕ diag(p⁻²colEnergy)) quadratic-form bound feeding the matrix-Khintchine trace-moment engine with normV = (sampled variance scale)². Candes-Recht 2009 (arXiv:0805.4471) Sec 6.1.

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.Basic
import Mathlib.Order.CompleteLattice.Finset
open Matrix
open scoped BigOperators

theorem block_diagonal_quadratic_form_le {n1 n2 : ℕ} (a : Fin n1 → ℝ) (b : Fin n2 → ℝ) (B : ℝ) (ha : ∀ i, a i ≤ B) (hb : ∀ j, b j ≤ B) (ha0 : ∀ i, (0:ℝ) ≤ a i) (hb0 : ∀ j, (0:ℝ) ≤ b j) (w : Fin n1 ⊕ Fin n2 → ℝ) : (star w ⬝ᵥ (Matrix.fromBlocks (diagonal a) 0 0 (diagonal b)) *ᵥ w) ≤ B * (star w ⬝ᵥ w) := by sorry
