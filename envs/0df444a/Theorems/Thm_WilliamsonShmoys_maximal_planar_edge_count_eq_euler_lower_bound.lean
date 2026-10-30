-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_eq_euler_lower_bound
-- name    : WilliamsonShmoys.maximal_planar_edge_count_eq_euler_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:53:25.548914+00:00
-- url     : https://prove2.me/theorems/2e7c0e9e-8922-4b6e-8b85-ae1ec34ad2dc
-- title:
--   Maximal planar edge lower bound for maximal edge-count theorem
-- statement:
--   A graph maximal among drawable supergraphs on the same vertex type, with at least three vertices, has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_eq_euler_lower_bound {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) (hCard : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
