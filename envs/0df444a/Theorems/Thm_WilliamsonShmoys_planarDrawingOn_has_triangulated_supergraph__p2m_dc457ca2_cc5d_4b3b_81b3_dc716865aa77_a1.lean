-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_has_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
-- name    : WilliamsonShmoys.planarDrawingOn_has_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:41:43.025127+00:00
-- url     : https://prove2.me/theorems/a025b1a8-d903-4a44-81b6-ec9f7e2f3e4a
-- title:
--   Augment a crossing-free drawing to a maximal planar graph
-- statement:
--   A finite simple graph with at least three vertices and the supplied crossing-free arc drawing can be extended, on the same vertex set, to a simple graph containing all its edges and having exactly 3|V|−6 edges. The lower bound on the vertex count is needed for triangulation and the stated edge formula; the drawing's injectivity, endpoint, interior, and non-crossing conditions are the geometric hypotheses to use.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawingOn_has_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := dG
     ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
       (letI : DecidableRel G.Adj := dG; letI : DecidableRel H.Adj := dH; G.edgeFinset ⊆ H.edgeFinset) ∧
       (letI : DecidableRel H.Adj := dH; H.edgeFinset.card = 3 * Fintype.card V - 6)) := by sorry
