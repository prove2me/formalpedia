-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_to_triangulation__p2m_75470aa8_21fb_4723_a0a9_53d10a7cd9b1_a1
-- name    : WilliamsonShmoys.planar_extension_to_triangulation__p2m_75470aa8_21fb_4723_a0a9_53d10a7cd9b1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:53:14.169197+00:00
-- url     : https://prove2.me/theorems/2f35ea45-99df-4cf1-95b2-81f89b32ddea
-- title:
--   Extend a finite planar drawing to a triangulation
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing on its ordered vertex type has a planar supergraph on the same vertex type with exactly 3|V|−6 edges. The lemma supplies the edge count directly, so it does not require the original graph to be connected or maximal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_to_triangulation__p2m_75470aa8_21fb_4723_a0a9_53d10a7cd9b1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hn : 3 <= Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel _
       K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
