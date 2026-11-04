-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planarDrawingOn_upper_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
-- name    : WilliamsonShmoys.edge_maximal_planarDrawingOn_upper_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:51:28.316975+00:00
-- url     : https://prove2.me/theorems/bc222e64-5fd0-4544-bad9-127a7d6f7d68
-- title:
--   Simple planar graph edge upper bound
-- statement:
--   Every finite simple graph with at least three vertices that has a crossing-free drawing has at most 3|V|−6 edges. The proof route is Euler’s formula together with the fact that each face has boundary length at least three in a simple planar embedding; the n=3 boundary case is included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planarDrawingOn_upper_bound__p2m_4f160dcf_31cc_41b6_9e73_2a2d16cdab21_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : HasPlanarDrawingOn H)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel H.Adj := dH; H.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
