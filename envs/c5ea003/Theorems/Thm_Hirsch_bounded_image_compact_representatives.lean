-- Prove2me | Theorems.Thm_Hirsch_bounded_image_compact_representatives
-- name    : Hirsch.bounded_image_compact_representatives
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-14T21:18:42.845626+00:00
-- url     : https://prove2.me/theorems/45f5569d-e24c-4a42-9572-de74ca0629c0
-- title:
--   Bounded polyhedral images admit uniform bounded nonnegative representatives
-- statement:
--   For every finite real resource map B and linear image map G, there is a positive constant C depending only on B and G such that every nonnegative x with Bx<=t has a nonnegative representative y with By<=t and Gy=Gx, total mass at most C*(norm(t)+norm(Gx)), and every coordinate-zero or tight resource row of x remains so at y. Consequently every uniformly bounded image of a resource polyhedron is unchanged after adding one sufficiently large total-mass bound; that capped coefficient set is compact. Neither original coefficient boundedness, injectivity of G, a coverage certificate, recession annihilation, nonemptiness, a vertex decomposition nor a right-inverse oracle is assumed. Constants are not claimed bounded by dimensions or rational bit complexity. This gives a compact representation of the same shape, not an ordinary-edge or diameter transport theorem.
-- source:
--   Classical finite-dimensional polyhedral geometry, proved directly by finite support descent and compact normalized coordinate sections. No Minkowski-Weyl, conic representation, uniform inverse-bound or coverage-existence oracle is assumed. The extremal-value lemma is Mathlib IsCompact.exists_isMinOn. This is the bounded-image representation gap identified after accepted #237, not a historical novelty claim or a new Hirsch diameter bound.

import Mathlib
open Set
open scoped BigOperators

namespace Hirsch
theorem bounded_image_compact_representatives {k r d : ℕ}
    (B : (Fin k → ℝ) →L[ℝ] (Fin r → ℝ))
    (G : (Fin k → ℝ) →L[ℝ] (Fin d → ℝ)) :
    (∃ C : ℝ, 0 < C ∧ ∀ (t : Fin r → ℝ) (x : Fin k → ℝ),
      (∀ i, 0 ≤ x i) → (∀ q, B x q ≤ t q) →
      ∃ y : Fin k → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ q, B y q ≤ t q) ∧
        G y = G x ∧ (∀ i, x i = 0 → y i = 0) ∧
        (∀ q, B x q = t q → B y q = t q) ∧
        (∑ i, y i) ≤ C * (‖t‖ + ‖G x‖)) ∧
    (∀ (t : Fin r → ℝ) (M : ℝ), 0 ≤ M →
      (∀ x : Fin k → ℝ, (∀ i, 0 ≤ x i) →
        (∀ q, B x q ≤ t q) → ‖G x‖ ≤ M) →
      ∃ R : ℝ, 0 ≤ R ∧
        IsCompact {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧
          (∀ q, B x q ≤ t q) ∧ (∑ i, x i) ≤ R} ∧
        G '' {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧ ∀ q, B x q ≤ t q} =
        G '' {x : Fin k → ℝ | (∀ i, 0 ≤ x i) ∧
          (∀ q, B x q ≤ t q) ∧ (∑ i, x i) ≤ R}) := by sorry
end Hirsch
