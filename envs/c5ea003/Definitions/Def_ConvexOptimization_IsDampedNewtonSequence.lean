-- Prove2me | Definitions.Def_ConvexOptimization_IsDampedNewtonSequence
-- name    : ConvexOptimization_IsDampedNewtonSequence
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-13T15:26:13.545762+00:00
-- url     : https://prove2.me/theorems/95bcb079-508d-414a-93a6-bece345f8c3c
-- title:
--   Damped Newton iteration with backtracking
-- statement:
--   A run of the **damped Newton method with backtracking line search** (B&V §9.5.2), described as a predicate on the sequence of iterates.
--
--   Fix a dimension $n$, a function $f : \mathbb{R}^n \to \mathbb{R}$, a gradient field $g : \mathbb{R}^n \to \mathbb{R}^n$, a Hessian field $H$ assigning to each point a continuous linear map $H(x) : \mathbb{R}^n \to \mathbb{R}^n$, and backtracking parameters $\alpha, \beta$. A sequence $(x_k)_{k \in \mathbb{N}}$ is a damped Newton sequence when for every $k$ there are a direction $\Delta$ and a step size $t$ with
--
--   $$H(x_k)\,\Delta = -g(x_k), \qquad t \text{ a backtracking step for } f \text{ at } x_k \text{ along } \Delta, \qquad x_{k+1} = x_k + t\,\Delta .$$
--
--   The first equation is the Newton system: $\Delta$ is the Newton step $-\nabla^2 f(x_k)^{-1}\nabla f(x_k)$, written as a linear equation so that no invertibility hypothesis has to be carried in the definition. The method is called *damped* because the line search may return $t < 1$; in the quadratically convergent phase it always returns $t = 1$.
--
--   Because the definition quantifies existentially over the direction and the step at each iteration, a theorem proved about damped Newton sequences applies to every faithful run of the algorithm, independently of how ties in the linear solve or the line search are broken.
--
--   **Formalization Note** The Hessian field has type `EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))`; the theorems using this definition add `∀ x, HasFDerivAt g (H x) x` to tie it to $f$. The backtracking condition is the separate predicate of B&V §9.2.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 487, §9.5.2 algorithm 9.5 (Newton's method with backtracking line search)

import Mathlib
import Definitions.Def_ConvexOptimization_IsBacktrackingStep

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- A damped-Newton iterate sequence with backtracking (B&V §9.5.2): each step
solves `H(xₖ) Δ = −g(xₖ)` and moves by a backtracking step size along `Δ`. -/
def IsDampedNewtonSequence {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (α β : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ k, ∃ (Δ : EuclideanSpace ℝ (Fin n)) (t : ℝ),
    H (x k) Δ = -g (x k) ∧ IsBacktrackingStep f g α β (x k) Δ t ∧
    x (k + 1) = x k + t • Δ

end ConvexOptimization


