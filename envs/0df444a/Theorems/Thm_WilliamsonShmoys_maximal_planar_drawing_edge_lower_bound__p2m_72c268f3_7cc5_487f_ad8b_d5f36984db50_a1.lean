-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:09:08.925632+00:00
-- url     : https://prove2.me/theorems/c6470163-a9cd-431f-b992-62a6706eed9c
-- title:
--   Lower edge bound for a maximal drawable graph
-- statement:
--   An inclusion maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges. This removes the maximality and face-completion argument from the parent; a route is to prove connectedness and triangular faces for a maximal drawing and apply Euler and face-edge incidence counting, with planar extension justified for the given arc drawing model.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_72c268f3_7cc5_487f_ad8b_d5f36984db50_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M →
      (∀ u v, L.Adj u v → M.Adj u v) →
      ∀ u v, M.Adj u v → L.Adj u v)
    (hcard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
