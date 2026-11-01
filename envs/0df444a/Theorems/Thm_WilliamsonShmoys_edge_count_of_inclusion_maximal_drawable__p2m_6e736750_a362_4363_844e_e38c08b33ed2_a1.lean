-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_inclusion_maximal_drawable__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
-- name    : WilliamsonShmoys.edge_count_of_inclusion_maximal_drawable__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:51:54.931888+00:00
-- url     : https://prove2.me/theorems/0d663055-40d3-4575-b5af-11ff2bc59459
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite ordered vertex type with at least three vertices has exactly `3n−6` edges. The hypothesis `n ≥ 3` covers the smallest case: for three vertices, maximality forces the triangle. A proof proceeds through the planar embedding and Euler’s formula, showing that maximality forces every face to be triangular.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_inclusion_maximal_drawable__p2m_6e736750_a362_4363_844e_e38c08b33ed2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (_hLdec : DecidableRel L.Adj),
      K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
