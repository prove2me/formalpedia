-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_a11205c3_51bf_4409_a8f2_455e7e17d8d2
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_a11205c3_51bf_4409_a8f2_455e7e17d8d2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:36:10.504681+00:00
-- url     : https://prove2.me/theorems/2db2ebfa-ce1d-48af-9002-4cb39330e2fb
-- title:
--   A finite planar graph has a maximal planar extension
-- statement:
--   Every planar graph on a finite vertex type has a planar supergraph on that same vertex set that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_a11205c3_51bf_4409_a8f2_455e7e17d8d2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        (∀ ⦃u v : V⦄, L.Adj u v → K.Adj u v) := by sorry
