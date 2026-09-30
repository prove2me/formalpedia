-- Prove2me | Theorems.Thm_Hirsch_common_face_diameter_of_dim_ge_four
-- name    : Hirsch.common_face_diameter_of_dim_ge_four
-- status  : Open
-- author  : @jjosh
-- created : 2026-09-11T02:29:23.863039+00:00
-- url     : https://prove2.me/theorems/07d89001-097d-41fa-8942-a09bf0990994
-- title:
--   Polynomial diameter of common faces of dimension at least four
-- statement:
--   A common face of dimension at least four has a polynomial combinatorial diameter in the number of inequalities and ambient dimension.
--
--   There exist constants $C,k$ such that the following holds. Let $P\subseteq\mathbb{R}^d$ be a bounded $n$-row H-polytope, and let $F=F(u,x)$ be a nonempty common face whose common-direction space has dimension $h\ge 4$. Then
--   $$
--   \operatorname{DiamLE}(F,\,C(n+d)^k).
--   $$
--   This is the remaining geometric content of high-carrier circuit-to-edge refinement: Klee already supplies a linear bound when $h\le 3$. The present statement does not follow from Kalai--Kleitman or Larman, which are the wrong growth rate.
--
--   **Formalization Note** Walks are padded. Natural-number exponentiation is used.
-- source:
--   Remaining geometric core of Hirsch.polynomial_edge_refinement_of_circuit_walks_of_high_carrier after Klee handles common faces of dimension at most three. No literature-priority claim; Kalai--Kleitman and Larman are the wrong growth.

import Definitions.Def_Hirsch_common_face_geometry

set_option autoImplicit false
open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch

theorem common_face_diameter_of_dim_ge_four :
    ∃ C k : ℕ, ∀ (d n : ℕ)
      (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
      (u x : EuclideanSpace ℝ (Fin d)),
      Bornology.IsBounded (Hpoly a b) →
      4 ≤ HirschCommonFace.commonFaceDim a b u x →
      (HirschCommonFace.commonFace a b u x).Nonempty →
      DiamLE (HirschCommonFace.commonFace a b u x) (C * (n + d) ^ k) := by sorry

end Hirsch
