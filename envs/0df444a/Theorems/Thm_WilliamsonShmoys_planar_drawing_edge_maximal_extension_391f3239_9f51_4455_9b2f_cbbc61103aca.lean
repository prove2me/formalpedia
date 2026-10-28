-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension_391f3239_9f51_4455_9b2f_cbbc61103aca
-- name    : WilliamsonShmoys.planar_drawing_edge_maximal_extension_391f3239_9f51_4455_9b2f_cbbc61103aca
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:29:52.178221+00:00
-- url     : https://prove2.me/theorems/d2cb493b-46a6-42b7-a416-6a95dd17b6ef
-- title:
--   Extension to a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_maximal_extension_391f3239_9f51_4455_9b2f_cbbc61103aca
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by sorry
