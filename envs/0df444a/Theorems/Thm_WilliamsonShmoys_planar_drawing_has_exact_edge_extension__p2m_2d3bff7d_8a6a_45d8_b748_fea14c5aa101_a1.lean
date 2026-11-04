-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_exact_edge_extension__p2m_2d3bff7d_8a6a_45d8_b748_fea14c5aa101_a1
-- name    : WilliamsonShmoys.planar_drawing_has_exact_edge_extension__p2m_2d3bff7d_8a6a_45d8_b748_fea14c5aa101_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:30:10.976969+00:00
-- url     : https://prove2.me/theorems/8f423dbe-14e3-49a1-828e-7cd49c2ddeb4
-- title:
--   Every finite planar drawing extends to a maximal planar graph with exactly 3n−6 edges
-- statement:
--   Any drawable graph on a finite linearly ordered vertex set of size at least three has a drawable supergraph on the same vertices with exactly 3n−6 edges. The parent’s maximality hypothesis forces this supergraph to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_exact_edge_extension__p2m_2d3bff7d_8a6a_45d8_b748_fea14c5aa101_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : WilliamsonShmoys.HasPlanarDrawingOn H) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 = K.edgeFinset.card := by sorry
