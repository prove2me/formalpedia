-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_from_triangulation
-- name    : WilliamsonShmoys.planar_edge_augmentation_from_triangulation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:43:50.265833+00:00
-- url     : https://prove2.me/theorems/ae5d92c8-a6bf-48b5-9322-d97a36242191
-- title:
--   Extract one drawable edge from a triangulated completion
-- statement:
--   Given a drawable graph below the planar edge bound and a drawable completion containing it with exactly 3|V|−6 edges, the graph can be extended by one edge while retaining drawability.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_from_triangulation
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hE : M.edgeSet.ncard < 3 * Fintype.card V - 6)
    (hT : ∃ T : SimpleGraph V, M ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6) :
    ∃ N : SimpleGraph V, M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard = M.edgeSet.ncard + 1 := by sorry
