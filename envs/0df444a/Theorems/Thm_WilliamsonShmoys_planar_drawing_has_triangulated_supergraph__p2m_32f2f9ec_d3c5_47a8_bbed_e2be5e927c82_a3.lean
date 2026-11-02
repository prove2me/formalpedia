-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulated_supergraph__p2m_32f2f9ec_d3c5_47a8_bbed_e2be5e927c82_a3
-- name    : WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_32f2f9ec_d3c5_47a8_bbed_e2be5e927c82_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:52:22.645996+00:00
-- url     : https://prove2.me/theorems/83bb3c80-7c1c-484d-89c0-d393ffbf355c
-- title:
--   Planar supergraph with triangulation edge count
-- statement:
--   Extend the given planar graph on the same vertices to a supergraph with the triangulation edge count. Its edge inclusion and monotonicity give the parent’s supergraph conditions; the edge equation lets the parent choose f = 2|V| − 4 and prove the two requested identities. The hypothesis |V| ≥ 3 covers the smallest case, where the extension is K₃. A proof route is to augment the drawing to a maximal planar graph, use maximality to obtain triangular faces, and combine Euler’s formula with face-edge incidence counting. This child removes that topological augmentation and counting work from the parent. The source reference gives the standard mathematical route; formalizing it for the exact continuous-arc predicate remains the core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_triangulated_supergraph__p2m_32f2f9ec_d3c5_47a8_bbed_e2be5e927c82_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      H.edgeFinset.card ≤ K.edgeFinset.card ∧
      K.edgeFinset.card + 6 = 3 * Fintype.card V := by
  sorry
