-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_2f35ea45_99df_4cf1_95b2_81f89b32ddea_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_2f35ea45_99df_4cf1_95b2_81f89b32ddea_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:50:23.787245+00:00
-- url     : https://prove2.me/theorems/f1c70f2e-734a-4ab3-9ef1-4b1e0b3c2cfc
-- title:
--   Finite planar graphs have a maximal planar supergraph
-- statement:
--   Every finite graph with a drawing has a same-vertex planar supergraph that has no strictly larger planar supergraph on that vertex type. This is obtained by maximizing the number of edges among the finite collection of planar supergraphs containing the input graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension__p2m_2f35ea45_99df_4cf1_95b2_81f89b32ddea_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
