-- Prove2me | Theorems.Thm_LinearOptimization_network_flow_integrality
-- name    : LinearOptimization.network_flow_integrality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T22:00:02.93118+00:00
-- url     : https://prove2.me/theorems/bf049b2f-49a6-4e9a-bda3-1cfbf301583f
-- title:
--   Integrality of basic solutions of network flow problems
-- statement:
--   **(Bertsimas & Tsitsiklis, Theorem 7.5, p. 289, GOAL)** Consider an uncapacitated network flow problem and assume that the underlying graph is connected.
--
--   - **(a)** For every basis matrix $\mathbf{B}$, the matrix $\mathbf{B}^{-1}$ has integer entries.
--   - **(b)** If the supplies $b_i$ are integer, then every basic solution has integer coordinates.
--   - **(c)** If the cost coefficients $c_{ij}$ are integer, then every dual basic solution has integer coordinates.
--
--   (Basis matrices are the nonsingular $(n-1)\times(n-1)$ submatrices of $\tilde{\mathbf{A}}$ formed by the columns of the $n-1$ arcs of a tree, cf. Theorems 7.3-7.4; basic solutions satisfy $\mathbf{f}_T=\mathbf{B}^{-1}\tilde{\mathbf{b}}$, dual basic solutions $\mathbf{p}'=\mathbf{c}_B'\mathbf{B}^{-1}$, p. 289. Standing Assumption 7.1(a): $\sum_{i\in\mathcal{N}}b_i=0$.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 7.5, p. 289

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Definitions.Def_BasicSolution


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 7.5 (p. 289).** Integrality for the uncapacitated
network flow problem `min c'f, Ãf = b̃, f ≥ 0` on a connected graph with
`∑ᵢ bᵢ = 0`: (a) every basis matrix of `Ã` has an integer inverse;
(b) integer supplies make every basic solution integer; (c) integer costs
make every dual basic solution `p' = c_B'B⁻¹` integer. -/

theorem LinearOptimization.network_flow_integrality {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1)) (bsupply : Fin (n + 1) → ℝ)
    (cost : Fin m → ℝ)
    (hloop : HasNoSelfLoops arcs) (hconn : IsConnectedNetwork arcs)
    (hsum : ∑ i, bsupply i = 0) :
    (∀ B : Fin n ↪ Fin m, IsStdBasis (truncatedIncidence arcs) B →
      ∀ i j, ∃ z : ℤ, (basisMatrix (truncatedIncidence arcs) B)⁻¹ i j = (z : ℝ)) ∧
    ((∀ i, ∃ z : ℤ, bsupply i = (z : ℝ)) →
      ∀ f, IsBasicSolution
          (stdFormSystem (truncatedIncidence arcs) (truncatedSupply bsupply)) f →
        ∀ k, ∃ z : ℤ, f k = (z : ℝ)) ∧
    ((∀ k, ∃ z : ℤ, cost k = (z : ℝ)) →
      ∀ B : Fin n ↪ Fin m, IsStdBasis (truncatedIncidence arcs) B →
        ∀ p : Fin n → ℝ,
          (basisMatrix (truncatedIncidence arcs) B)ᵀ.mulVec p =
            (fun i => cost (B i)) →
          ∀ i, ∃ z : ℤ, p i = (z : ℝ)) := by
  sorry
