-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:14.410027+00:00
-- url     : https://prove2.me/theorems/c129c456-fb95-4993-b973-699ff9e1cc14
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   A finite graph with a planar drawing has a supergraph on the same vertices that is maximal among planar supergraphs and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_25a042c7_1a1b_47c9_a392_cae86f15b395_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
