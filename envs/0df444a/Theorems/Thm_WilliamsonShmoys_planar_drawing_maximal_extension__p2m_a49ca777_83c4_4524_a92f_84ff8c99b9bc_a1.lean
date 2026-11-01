-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:38:26.608141+00:00
-- url     : https://prove2.me/theorems/ad0a6ea0-cb80-4e05-87dc-f915114ec2a9
-- title:
--   Extend a planar drawing to a maximal planar graph
-- statement:
--   Every finite simple graph with the given kind of planar drawing is a subgraph of a maximal planar graph on the same vertex type, with at least as many edges. Maximal means no strictly larger supergraph on those vertices has such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_a49ca777_83c4_4524_a92f_84ff8c99b9bc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
      (letI : DecidableRel G.Adj := Classical.decRel _
       letI : DecidableRel H.Adj := Classical.decRel _
       G.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
