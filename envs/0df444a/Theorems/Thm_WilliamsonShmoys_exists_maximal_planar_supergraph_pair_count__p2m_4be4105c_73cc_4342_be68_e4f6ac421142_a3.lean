-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_pair_count__p2m_4be4105c_73cc_4342_be68_e4f6ac421142_a3
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_pair_count__p2m_4be4105c_73cc_4342_be68_e4f6ac421142_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:09:05.565213+00:00
-- url     : https://prove2.me/theorems/1754312f-1a0e-4ba7-b888-5b49fae17caa
-- title:
--   Finite pair-count-maximal drawable extension
-- statement:
--   There is a drawable supergraph K of H whose number of ordered adjacent vertex pairs is at least that of every drawable extension L of K. The child isolates the finite maximization step; inclusion and the reverse cardinal bound imply that each such extension has the same adjacency relation as K.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open Classical

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_pair_count__p2m_4be4105c_73cc_4342_be68_e4f6ac421142_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V,
        (∀ u v, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        (Finset.univ.filter (fun p : V × V => L.Adj p.1 p.2)).card ≤
          (Finset.univ.filter (fun p : V × V => K.Adj p.1 p.2)).card := by sorry
