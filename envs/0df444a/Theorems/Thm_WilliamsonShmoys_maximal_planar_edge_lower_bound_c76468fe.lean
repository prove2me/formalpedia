-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_c76468fe
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_c76468fe
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:47:21.83045+00:00
-- url     : https://prove2.me/theorems/ea79ad5a-1bf7-418b-95e2-18c46e816865
-- title:
--   Lower bound for maximal planar graphs
-- statement:
--   A graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_c76468fe {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) (hCard : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
