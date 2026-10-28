-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_edge_lower_bound
-- name    : WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T02:49:30.194986+00:00
-- url     : https://prove2.me/theorems/d7e64e6f-4cfb-4483-a52e-a20945c5a3c5
-- title:
--   Planar augmentation with the maximal planar edge lower bound
-- statement:
--   Any finite drawable simple graph on at least three fixed vertices has a drawable supergraph on those same vertices with at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_supergraph_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      3 * Fintype.card V - 6 ≤ P.edgeSet.ncard := by sorry
