-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_inclusion_maximal_planar_supergraph__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
-- name    : WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:48:25.123282+00:00
-- url     : https://prove2.me/theorems/65e72c44-7343-44e8-af99-15a893a2929a
-- title:
--   Existence of an inclusion maximal drawable supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertex type that is inclusion maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.exists_inclusion_maximal_planar_supergraph__p2m_4b265a90_b8bd_4522_9040_b7d7632358e1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M := by sorry
