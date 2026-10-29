-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_faceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3
-- name    : WilliamsonShmoys.planarDrawingOn_faceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:52:36.536836+00:00
-- url     : https://prove2.me/theorems/c137e21e-1857-4be7-8a5c-d493c2550e04
-- title:
--   Face-count data from a connected planar drawing
-- statement:
--   A connected simple graph on at least three vertices with the supplied crossing-free drawing has a finite face-count certificate: each face boundary has length at least three, total boundary length is twice the number of edges, and the vertex and face counts satisfy Euler’s relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarFaceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_faceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    WilliamsonShmoys.HasPlanarFaceCountData__p2m_b6739023_548b_4b2e_a781_9b00cc5e2c81_a3 G := by sorry
