-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_drawing_is_dense
-- name    : WilliamsonShmoys.edge_maximal_planar_drawing_is_dense
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:16:58.033266+00:00
-- url     : https://prove2.me/theorems/572903dc-85c6-49e9-9710-c32e95b4c977
-- title:
--   An edge maximal drawable graph has the planar density bound
-- statement:
--   A drawable finite simple graph on at least three vertices that has no strictly larger drawable supergraph has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_drawing_is_dense
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet = K.edgeSet) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  sorry
