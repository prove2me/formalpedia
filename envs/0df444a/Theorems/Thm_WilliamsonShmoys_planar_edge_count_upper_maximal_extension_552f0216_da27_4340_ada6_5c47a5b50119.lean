-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_maximal_extension_552f0216_da27_4340_ada6_5c47a5b50119
-- name    : WilliamsonShmoys.planar_edge_count_upper_maximal_extension_552f0216_da27_4340_ada6_5c47a5b50119
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:14:38.724058+00:00
-- url     : https://prove2.me/theorems/d6e22aee-36ed-47ad-aadb-1acc358b79ef
-- title:
--   Maximal drawable extension for the edge bound
-- statement:
--   A drawable graph on a finite vertex type is contained in a drawable supergraph that is maximal among drawable supergraphs on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_maximal_extension_552f0216_da27_4340_ada6_5c47a5b50119 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ ∀ H' : SimpleGraph V, H ≤ H' → WilliamsonShmoys.HasPlanarDrawingOn H' → H' = H := by sorry
