-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_connected_supergraph_geometric_step__p2m_e22a771a_7e28_4296_9438_b0a9d74716aa_a2
-- name    : WilliamsonShmoys.planarDrawing_connected_supergraph_geometric_step__p2m_e22a771a_7e28_4296_9438_b0a9d74716aa_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:08:29.312809+00:00
-- url     : https://prove2.me/theorems/6e806989-c014-4a7f-8d5e-17d89f0fc271
-- title:
--   Connect a planar drawing by a drawable supergraph
-- statement:
--   A finite drawable graph on at least three vertices has a connected drawable supergraph on the same vertices, retaining every original edge and therefore having at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_connected_supergraph_geometric_step__p2m_e22a771a_7e28_4296_9438_b0a9d74716aa_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ HasPlanarDrawingOn H ∧
        K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
