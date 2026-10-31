-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:50:00.289418+00:00
-- url     : https://prove2.me/theorems/d0c0f93a-bf39-4f1e-a2a5-4287530c2a04
-- title:
--   Existence of an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph is contained in a drawable graph on the same vertices that has no proper drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_3a18cd50_a833_4853_9055_3e93726fc3e4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph V,
      G ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ H : SimpleGraph V, M ≤ H → HasPlanarDrawingOn H → H = M := by sorry
