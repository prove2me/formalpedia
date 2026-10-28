-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:45:54.814164+00:00
-- url     : https://prove2.me/theorems/4732a484-624b-4d6f-8ae2-d5e94b659ca5
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that has no strictly larger drawable supergraph. Choose a drawable supergraph with greatest edge-set cardinality. Any strict graph extension adds an edge, contradicting maximal cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N := by sorry
