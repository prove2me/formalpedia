-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_connected__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_connected__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:11.675091+00:00
-- url     : https://prove2.me/theorems/b0b687f8-4cc8-496c-af1a-60542cca02f0
-- title:
--   Maximal planar drawing implies connectedness
-- statement:
--   If a graph on at least three vertices has a crossing-free drawing and has no strictly larger planar supergraph on the same vertex set, then it is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_connected__p2m_6a6f73b1_aafd_4ec3_b910_d68356c6d6db_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G)
    (hcard : 3 ≤ Fintype.card V) :
    G.Connected := by sorry
