-- Prove2me | Theorems.Thm_ZeroOneExpansion_fact_6
-- name    : ZeroOneExpansion.fact_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:21:30.624197+00:00
-- url     : https://prove2.me/theorems/71d481a5-2933-4944-aeb9-9f3f39c4fcb7
-- title:
--   Fact 6 — cross-layer edges of a Cayley sum
-- statement:
--   Let $A,B\subseteq\mathbb R^d$ be finite and nonempty, and let $a_0\in A$, $b_0\in B$. The segment $[(a_0,0),(b_0,1)]$ is an edge of $A*B$ if and only if there exists $w\in\mathbb R^d$ such that $x\mapsto w\cdot x$ is uniquely maximized over $A$ at $a_0$ and over $B$ at $b_0$.
--
--   This reduces the cross-layer edges of $P_n=X_n*Y_n$ to a simultaneous unique-maximizer condition (Corollary 10).
--
--   Differences from the source:
--   - encoding: "[u, v] is an edge" (a one-dimensional face) → the segment [u, v] is a face (IsExposed ℝ P (segment ℝ u v)); reason: the two endpoints are distinct, so the segment is one-dimensional, and a one-dimensional face is an edge
--   - encoding: x ↦ w·x is uniquely maximized over A at a₀ → ∀ a ∈ A, a ≠ a₀ → w·a < w·a₀; reason: the definition of a unique maximizer
--   - encoding: A, B ⊆ ℝ^d finite → A, B Finsets; reason: the same sets
--   - encoding: (x, t) ∈ ℝ^d × ℝ → withLast x t ∈ Fin (d+1) → ℝ, t the last coordinate; reason: the same space
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), Fact 6, p.4

import Mathlib
import Definitions.Def_ZeroOneExpansion_cayleySum

set_option autoImplicit false

open Matrix

namespace ZeroOneExpansion

/-- **Fact 6** (Yang, *0/1-Polytopes with Exponentially Small Edge Expansion*, arXiv:2608.01870, p.4). Let `A, B ⊆ ℝ^d` be finite and nonempty, `a₀ ∈ A`, `b₀ ∈ B`. The
segment `[(a₀, 0), (b₀, 1)]` is an edge of `A ∗ B` iff there is `w ∈ ℝ^d` such that `x ↦ w · x` is
uniquely maximized over `A` at `a₀` and over `B` at `b₀`.

**Formalization Note** "The segment is an edge" is "the segment is a face" (`IsExposed`, a maximizer
set of a linear functional): its endpoints have different last coordinates, so the segment is
one-dimensional, and a one-dimensional face is an edge. "Uniquely maximized over `A` at `a₀`" is
`∀ a ∈ A, a ≠ a₀ → w · a < w · a₀`. -/
theorem fact_6 {d : ℕ} (A B : Finset (Fin d → ℝ)) (hA : A.Nonempty) (hB : B.Nonempty)
    (a₀ b₀ : Fin d → ℝ) (ha : a₀ ∈ A) (hb : b₀ ∈ B) :
    IsExposed ℝ (cayleySum (A : Set (Fin d → ℝ)) (B : Set (Fin d → ℝ)))
        (segment ℝ (withLast a₀ 0) (withLast b₀ 1)) ↔
      ∃ w : Fin d → ℝ, (∀ a ∈ A, a ≠ a₀ → w ⬝ᵥ a < w ⬝ᵥ a₀) ∧
        (∀ b ∈ B, b ≠ b₀ → w ⬝ᵥ b < w ⬝ᵥ b₀) := by sorry

end ZeroOneExpansion
