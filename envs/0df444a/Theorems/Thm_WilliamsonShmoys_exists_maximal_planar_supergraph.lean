-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:31:39.549013+00:00
-- url     : https://prove2.me/theorems/751ee02a-aeaa-4ce2-804e-73d4c044cdb6
-- title:
--   A planar graph has an edge-maximal planar supergraph
-- statement:
--   Every finite planar graph on an ordered finite vertex type has a planar supergraph on the same vertices whose edge count is at least that of every planar supergraph of it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ H : SimpleGraph V,
        (∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn H →
        H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
