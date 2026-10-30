-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_extension__p2m_4d39bfdd_3b15_4c53_aa35_0f292c6309dd_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_extension__p2m_4d39bfdd_3b15_4c53_aa35_0f292c6309dd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:48:22.437583+00:00
-- url     : https://prove2.me/theorems/03072eec-b341-4d2a-bf51-52bbec077883
-- title:
--   Augmenting a disconnected planar drawing
-- statement:
--   Every disconnected finite graph with the supplied planar drawing and at least three vertices has a drawable strict edge supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planar_drawing_edge_extension__p2m_4d39bfdd_3b15_4c53_aa35_0f292c6309dd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hdis : ¬ K.Connected) :
    ∃ (L : SimpleGraph V) (hLdec : DecidableRel L.Adj),
      K.edgeFinset ⊂ L.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
