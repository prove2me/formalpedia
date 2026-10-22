-- Prove2me | Theorems.Thm_WrightPDIPM_SelfDual_theorem_A_1
-- name    : WrightPDIPM.SelfDual.theorem_A_1
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:56:15.99089+00:00
-- url     : https://prove2.me/theorems/82e975d6-b572-4254-9d4f-0765adcf416a
-- title:
--   Theorem A.1 — KKT conditions are necessary at a local solution of a linearly constrained problem
-- statement:
--   Let $U \subset \mathbb R^N$ be open, $f : \mathbb R^N \to \mathbb R$, $C \in \mathbb R^{k\times N}$, $d \in \mathbb R^k$, $G \in \mathbb R^{l\times N}$, $h \in \mathbb R^l$, and consider the problem
--   $$\min_u f(u) \quad\text{subject to}\quad Cu = d,\ Gu \ge h,\ u \in U. \qquad (A.2)$$
--   Suppose $u^*$ is a local solution of (A.2) (feasible, and $f(u) \ge f(u^*)$ for all feasible $u$ with $\|u - u^*\| < \rho$, for some $\rho > 0$) and that $f$ is differentiable in a neighborhood of $u^*$. Then there are vectors $y \in \mathbb R^k$ and $z \in \mathbb R^l$ such that
--   $$\nabla f(u^*) - C^{\mathsf T}y - G^{\mathsf T}z = 0,\quad Cu^* = d,\quad Gu^* \ge h,\quad z \ge 0,\quad z^{\mathsf T}(Gu^* - h) = 0. \qquad (A.3)$$
--
--   These are the first-order (Karush–Kuhn–Tucker) necessary conditions; for linear constraints no constraint qualification is needed. Applied to the self-dual program (9.1), they produce the system from which the mixed LCP (9.2) is derived.
--
--   **Formalization Note** $\|\cdot\|$ is the Euclidean norm; $\nabla f(u^*)$ is the vector of Fréchet partial derivatives. "Differentiable in a neighborhood of $u^*$" is `∀ᶠ u in nhds u*, DifferentiableAt ℝ f u`.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, pp. 240–241, Theorem A.1

import Mathlib
import Definitions.Def_WrightPDIPM_SelfDual_Setup

namespace WrightPDIPM.SelfDual

open Matrix

/-- Theorem A.1 (pp. 240–241): if `u*` is a local solution of (A.2)
`min f(u) s.t. Cu = d, Gu ≥ h, u ∈ U` (`U ⊂ ℝᴺ` open) and `f` is differentiable in a
neighborhood of `u*`, then there are Lagrange multipliers `y`, `z` with (A.3a)
`∇f(u*) − Cᵀy − Gᵀz = 0`, (A.3b) `Cu* = d`, (A.3c) `Gu* ≥ h`, (A.3d) `z ≥ 0`,
(A.3e) `zᵀ(Gu* − h) = 0`. -/
theorem theorem_A_1 {N k l : ℕ} (f : (Fin N → ℝ) → ℝ) (C : Matrix (Fin k) (Fin N) ℝ)
    (d : Fin k → ℝ) (G : Matrix (Fin l) (Fin N) ℝ) (h : Fin l → ℝ) (U : Set (Fin N → ℝ))
    (hU : IsOpen U) (ustar : Fin N → ℝ) (hloc : IsLocalSolutionA2 f C d G h U ustar)
    (hdiff : ∀ᶠ u in nhds ustar, DifferentiableAt ℝ f u) :
    ∃ (y : Fin k → ℝ) (z : Fin l → ℝ),
      gradVec f ustar - Cᵀ *ᵥ y - Gᵀ *ᵥ z = 0 ∧
      C *ᵥ ustar = d ∧
      (∀ i, h i ≤ (G *ᵥ ustar) i) ∧
      (∀ i, 0 ≤ z i) ∧
      z ⬝ᵥ (G *ᵥ ustar - h) = 0 := by sorry

end WrightPDIPM.SelfDual
