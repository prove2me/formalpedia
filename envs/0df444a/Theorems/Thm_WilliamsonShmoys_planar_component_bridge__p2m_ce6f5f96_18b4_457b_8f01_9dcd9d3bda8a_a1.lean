-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_bridge__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
-- name    : WilliamsonShmoys.planar_component_bridge__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T07:18:28.417159+00:00
-- url     : https://prove2.me/theorems/9b66867f-d114-4813-a17a-8c314563f22e
-- title:
--   Add a drawable edge between planar components
-- statement:
--   A finite drawable graph on at least three vertices that is disconnected has a strict drawable supergraph on the same vertices. The added edge can join two distinct components while preserving a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_component_bridge__p2m_ce6f5f96_18b4_457b_8f01_9dcd9d3bda8a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hDisconnected : ¬ K.Connected) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ K.edgeSet ⊂ L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
