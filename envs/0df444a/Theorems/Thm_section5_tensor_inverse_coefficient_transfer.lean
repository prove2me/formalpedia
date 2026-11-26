-- Prove2me | Theorems.Thm_section5_tensor_inverse_coefficient_transfer
-- name    : section5_tensor_inverse_coefficient_transfer
-- status  : Proved
-- author  : @stockfish-soup
-- created : 2026-11-26T19:59:23.614844+00:00
-- url     : https://prove2.me/theorems/4f2f6538-b24a-4d17-95e6-45fddb441206
-- title:
--   Conditional tensor inverse coefficient transfer
-- statement:
--   Let $A,S:\mathbb C^{\alpha}\to\mathbb C^{\beta}$ be linear operators between finite Euclidean spaces, let $n\ge1$, and let $0<\eta<1/2$. Assume $\|A\|\le1$ and $\|A-S\|\le\eta/(4n)$. For a vector $\psi\in\mathbb C^{\beta^n}$ with $\|\psi\|\le1$ and any $c\in\mathbb C^{\alpha^n}$, the following implication holds:
--
--   $$\|(S^{\otimes n})^*\psi-c\|\le\eta/2\quad\Longrightarrow\quad\|(A^{\otimes n})^*\psi-c\|\le\eta.$$
--
--   This transfers a coefficient estimate from an approximate synthesis map to another specified map; the approximation hypotheses are part of the statement.
-- source:
--   Original auxiliary coefficient-transfer result for Krivcenko, Nguyen and de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, https://arxiv.org/html/2609.40331v3, Section 5.1. Formalization: Solutions/Section5HermiteTransfer.lean, lines 347–358.

import Definitions.Def_Section5Verified_Section5HermiteTransfer
import Mathlib
set_option autoImplicit false

theorem section5_tensor_inverse_coefficient_transfer
    {α β : Type*} [Fintype α] [Fintype β]
    (A S : EuclideanSpace ℂ α →L[ℂ] EuclideanSpace ℂ β)
    (n : ℕ) (hn : 1 ≤ n) (η : ℝ) (hη : 0 < η) (hη' : η < 1/2)
    (hA : ‖A‖ ≤ 1) (hAS : ‖A-S‖ ≤ η/(4*n))
    (ψ : EuclideanSpace ℂ (Fin n → β)) (hψ : ‖ψ‖ ≤ 1)
    (c : EuclideanSpace ℂ (Fin n → α))
    (hdisc : ‖ContinuousLinearMap.adjoint (section5_tensor_power S n) ψ-c‖ ≤ η/2) :
    ‖ContinuousLinearMap.adjoint (section5_tensor_power A n) ψ-c‖ ≤ η := by sorry
