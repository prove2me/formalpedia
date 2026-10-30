-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_noncomplete_strict_extension__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
-- name    : WilliamsonShmoys.planar_graph_noncomplete_strict_extension__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:04:11.94691+00:00
-- url     : https://prove2.me/theorems/87c3be14-3a1d-4b7c-94e8-aabf74fa2cf8
-- title:
--   A noncomplete planar graph has a strict planar extension
-- statement:
--   Any noncomplete finite planar graph with at least three vertices has a strict planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_noncomplete_strict_extension__p2m_60d14aea_be69_4b51_a6fb_6f45c6ceb723_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hNoncomplete : ¬ ∀ u v : V, u ≠ v → H.Adj u v) :
    ∃ M : SimpleGraph V,
      H ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ M ≠ H := by sorry
