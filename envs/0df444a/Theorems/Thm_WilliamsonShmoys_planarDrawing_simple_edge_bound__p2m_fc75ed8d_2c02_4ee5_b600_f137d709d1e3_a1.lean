-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_simple_edge_bound__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
-- name    : WilliamsonShmoys.planarDrawing_simple_edge_bound__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:15.005601+00:00
-- url     : https://prove2.me/theorems/4ec6bc0b-ec8a-4e25-875f-9ac5631f6eca
-- title:
--   Simple planar edge bound
-- statement:
--   A finite connected simple graph with the supplied crossing-free drawing and at least three vertices has at most 3n − 6 edges. This removes the extremal edge-count step from the parent. A proof route is to count edge incidences along face boundary walks: each edge contributes twice, and simplicity together with the connectedness and size hypotheses ensures each face walk has length at least three. Prove the required face-count and incidence identities within this child, so it has no dependency on the proposed Euler child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_simple_edge_bound__p2m_fc75ed8d_2c02_4ee5_b600_f137d709d1e3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 6 ≤
      3 * Fintype.card V := by sorry
