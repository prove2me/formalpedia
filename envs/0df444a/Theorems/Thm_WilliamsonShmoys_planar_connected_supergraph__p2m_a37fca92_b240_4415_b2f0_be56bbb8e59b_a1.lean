-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1
-- name    : WilliamsonShmoys.planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:47:51.225566+00:00
-- url     : https://prove2.me/theorems/4a4e7efe-f553-4450-ba1c-24b78e833049
-- title:
--   Connected planar supergraph on the same vertices
-- statement:
--   A finite drawn simple graph with at least three vertices can be extended by adding edges, on the same vertices, to a connected graph that still has a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_supergraph__p2m_a37fca92_b240_4415_b2f0_be56bbb8e59b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      K.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
