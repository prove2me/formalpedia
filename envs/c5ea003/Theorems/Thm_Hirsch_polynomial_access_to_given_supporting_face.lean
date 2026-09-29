-- Prove2me | Theorems.Thm_Hirsch_polynomial_access_to_given_supporting_face
-- name    : Hirsch.polynomial_access_to_given_supporting_face
-- status  : Open
-- author  : @WillR
-- created : 2026-09-06T12:39:58.339778+00:00
-- url     : https://prove2.me/theorems/33fc334e-e05b-4090-ac49-f83fd94d9305
-- title:
--   Polynomial routing to a prescribed supporting face
-- statement:
--   Uniformly route to a specified supporting face. There exist natural numbers $C,k$, independent of the H-polytope, such that whenever $P=\{x:\langle a_j,xangle\le b_j\}$ is bounded, $u
--   e v$ are extreme points, and no nonzero row is tight at both endpoints, every supplied nonzero row $i$ tight at $v$ contains an extreme point $z$ reachable from $u$ by a padded vertex-edge walk of length at most
--
--   $$
--   C(n+d)^k,
--   $$
--
--   with $\langle a_i,zangle=b_i$. The row $i$ is part of the input, so this isolates the genuine routing problem from the elementary fact that a distinct target vertex has a nonzero supporting row.
--
--   This is a reusable strengthening of the mission’s `polynomial_target_face_access`: solving it supplies the parent theorem for any row selected by the support lemma, while preserving redundant inequalities, zero-normal rows, lower-dimensional polytopes, and stationary walk steps.
--
--   **Formalization Note** The Lean statement is intentionally identical to the mission target except that the supporting row `i` is supplied as a hypothesis and the conclusion routes to that same row.
-- source:
--   Derived routing subproblem for Prove2Me `Hirsch.polynomial_target_face_access`, in the decomposition of Kalai’s polynomial Hirsch conjecture; context Kalai (Polymath 3, 2010) and Santos, TOP 21 (2013), arXiv:1307.5900, Conjecture 1.1.

import Definitions.Def_Hirsch_model

open scoped RealInnerProductSpace

namespace Hirsch

theorem polynomial_access_to_given_supporting_face :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      Bornology.IsBounded (Hpoly a b) →
      ∀ u ∈ Set.extremePoints ℝ (Hpoly a b),
      ∀ v ∈ Set.extremePoints ℝ (Hpoly a b), u ≠ v →
      (∀ j, a j ≠ 0 → ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) →
      ∀ i : Fin n, a i ≠ 0 → ⟪a i, v⟫ = b i →
      ∃ z : EuclideanSpace ℝ (Fin d),
        z ∈ Set.extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
        ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
          w 0 = u ∧ w (C * (n + d) ^ k) = z ∧
          ∀ j < C * (n + d) ^ k,
            w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by sorry

end Hirsch
