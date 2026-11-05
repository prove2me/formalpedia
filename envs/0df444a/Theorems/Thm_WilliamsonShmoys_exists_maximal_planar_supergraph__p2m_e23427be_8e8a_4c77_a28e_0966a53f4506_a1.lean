-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:00.480385+00:00
-- url     : https://prove2.me/theorems/b6765847-4b48-4473-801c-ad92c775fb51
-- title:
--   Extension to an edge-maximal planar supergraph
-- statement:
--   Every graph with the given planar drawing is contained in an edge-maximal planar graph on the same finite vertex type, with at least as many edges. The maximality condition says every planar supergraph on that vertex type is already a subgraph of H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_e23427be_8e8a_4c77_a28e_0966a53f4506_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ H : SimpleGraph V,
      N ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      N.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) := by sorry
