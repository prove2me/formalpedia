-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exists_maximal_9064c577_retry2
-- name    : WilliamsonShmoys.planar_supergraph_exists_maximal_9064c577_retry2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:14:53.185925+00:00
-- url     : https://prove2.me/theorems/4214d666-e73d-4f54-862a-5e1512344a6a
-- title:
--   A finite drawable supergraph can be chosen maximal
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs. Finiteness supplies a maximizer of edge count, and the graph H itself ensures the candidate set is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_exists_maximal_9064c577_retry2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by sorry
