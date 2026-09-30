-- Prove2me | Theorems.Thm_HirschCircuit_exists_positive_maximal_nonnegative_step
-- name    : HirschCircuit.exists_positive_maximal_nonnegative_step
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-08T18:50:27.42079+00:00
-- url     : https://prove2.me/theorems/ac00e416-0658-485d-9a4a-1cbeac8b26a4
-- title:
--   Existence of a positive maximal nonnegative augmentation
-- statement:
--   Let $x\in\mathbb R^n_{\ge0}$ and let $g$ be a direction that is nonnegative at every coordinate where $x$ is zero, but is negative in at least one coordinate. Then there is a strictly positive maximal step length $\alpha$: $x+\alpha g$ remains nonnegative, at least one decreasing coordinate becomes zero, and every larger step violates nonnegativity. The step is the minimum blocking ratio over the finitely many negative coordinates of $g$.
-- source:
--   Elementary finite-minimum maximal-augmentation lemma used in the support-safe adaptation of Bento Natura, Circuit Diameter of Polyhedra is Strongly Polynomial, arXiv:2602.06958v2, Section 1.1 and Algorithm 1.

import Mathlib

set_option autoImplicit false

namespace HirschCircuit

theorem exists_positive_maximal_nonnegative_step {n : ℕ}
    (x g : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hzero : ∀ i, x i = 0 → 0 ≤ g i)
    (hneg : ∃ i, g i < 0) :
    ∃ α : ℝ, 0 < α ∧ (∀ i, 0 ≤ x i + α * g i) ∧
      (∃ q, g q < 0 ∧ x q + α * g q = 0) ∧
      ∀ β : ℝ, α < β → ∃ i, x i + β * g i < 0 := by sorry

end HirschCircuit
