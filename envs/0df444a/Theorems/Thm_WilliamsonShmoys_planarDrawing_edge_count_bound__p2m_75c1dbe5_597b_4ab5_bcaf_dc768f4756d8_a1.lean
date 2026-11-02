-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_edge_count_bound__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
-- name    : WilliamsonShmoys.planarDrawing_edge_count_bound__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:05:27.971262+00:00
-- url     : https://prove2.me/theorems/15e1d124-3e67-41bc-8403-c26ff4c383cc
-- title:
--   Simple planar edge bound from a drawing
-- statement:
--   A finite simple graph with at least three vertices and the supplied crossing-free drawing has at most 3|V|−6 edges. The bound is sharp for a drawn triangle and remains valid for disconnected graphs. One independent route is to apply Euler’s formula componentwise, count edge-side incidences around face boundary walks (counting both sides of bridges), and use that each face boundary has length at least three after handling tree and small-component cases. This removes the planar density estimate from the parent; the remaining work for this child is proving the incidence accounting and treating its boundary cases for the exact drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_edge_count_bound__p2m_75c1dbe5_597b_4ab5_bcaf_dc768f4756d8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (dU : DecidableRel U.Adj)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel U.Adj := dU
     U.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
