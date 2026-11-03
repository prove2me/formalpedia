-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarEdgeBound__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1
-- name    : WilliamsonShmoys.planarEdgeBound__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:45.364024+00:00
-- url     : https://prove2.me/theorems/d0c9e92c-0850-4f5e-91b8-72d4ab522367
-- title:
--   Planar graph edge bound for at least three vertices
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The boundary condition excludes the small-vertex cases where this bound is inappropriate. An independent proof route is to establish connected-component or face-counting bounds from the drawing, apply Euler’s formula, and account for the fact that a simple planar graph has no face boundary of length one or two, handling bridges and disconnected graphs explicitly. This supplies the upper-bound side of the target argument; the remaining issue for the target is obtaining a planar supergraph with the full count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarEdgeBound__p2m_21a5024a_68c6_4092_ae33_cef64e9ed718_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hn : 3 ≤ Fintype.card V) :
    (letI : DecidableRel L.Adj := dL
     L.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry
