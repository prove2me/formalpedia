-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_extension__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2__p2m_af83aa0e_dfa3_4817_a80f_86472a8bb5ad_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2__p2m_af83aa0e_dfa3_4817_a80f_86472a8bb5ad_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:44:04.953778+00:00
-- url     : https://prove2.me/theorems/5f4c0396-f2c5-4ee4-89c1-d7bcb4050c5c
-- title:
--   Finite edge-count maximizer among drawable supergraphs
-- statement:
--   Among drawable supergraphs of a given drawable finite graph, there is one whose edge count is at least that of every other drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_maximal_extension__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2__p2m_af83aa0e_dfa3_4817_a80f_86472a8bb5ad_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, L ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, L ≤ K → HasPlanarDrawingOn K →
        K.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
