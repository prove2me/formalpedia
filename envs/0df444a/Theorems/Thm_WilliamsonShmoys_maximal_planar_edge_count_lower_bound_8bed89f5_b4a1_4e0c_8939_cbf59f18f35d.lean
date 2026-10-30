-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:05:40.167988+00:00
-- url     : https://prove2.me/theorems/a9d6da29-ff69-465c-9a71-ac972a1190c4
-- title:
--   Maximal planar graph edge lower bound for this target
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_8bed89f5_b4a1_4e0c_8939_cbf59f18f35d
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ R : SimpleGraph V,
      M ≤ R →
      WilliamsonShmoys.HasPlanarDrawingOn R →
      R ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry
