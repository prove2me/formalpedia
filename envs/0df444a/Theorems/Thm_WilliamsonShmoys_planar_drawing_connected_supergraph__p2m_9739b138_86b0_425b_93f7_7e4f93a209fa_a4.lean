-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_supergraph__p2m_9739b138_86b0_425b_93f7_7e4f93a209fa_a4
-- name    : WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_9739b138_86b0_425b_93f7_7e4f93a209fa_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:26:54.940232+00:00
-- url     : https://prove2.me/theorems/e12d1ce4-d402-4aed-8f60-36f6bfa13375
-- title:
--   Extend a planar drawing to a connected supergraph
-- statement:
--   Any graph on the finite ordered vertex type that has a crossing-free drawing has a connected supergraph on that same vertex type with a crossing-free drawing. The result isolates the geometric extension and leaves edge-count monotonicity to a separate finite-graph lemma.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_supergraph__p2m_9739b138_86b0_425b_93f7_7e4f93a209fa_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V,
      (∀ u v, L.Adj u v → H.Adj u v) ∧
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
