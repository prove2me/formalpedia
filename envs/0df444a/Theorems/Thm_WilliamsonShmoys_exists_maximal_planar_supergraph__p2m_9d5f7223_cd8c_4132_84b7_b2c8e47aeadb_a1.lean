-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:17:51.287992+00:00
-- url     : https://prove2.me/theorems/465037e3-08d8-4599-8b26-f505e0dc287e
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertex set that admits no proper drawable supergraph on that vertex set. This removes finite maximization and the existence portion of augmentation from the parent. Prove it by considering the finite family of simple graphs containing G that have a drawing, which is nonempty by hG, and choosing one with maximum edge-set cardinality. The parent still needs the edge bound for maximal drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9d5f7223_cd8c_4132_84b7_b2c8e47aeadb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ u v, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
