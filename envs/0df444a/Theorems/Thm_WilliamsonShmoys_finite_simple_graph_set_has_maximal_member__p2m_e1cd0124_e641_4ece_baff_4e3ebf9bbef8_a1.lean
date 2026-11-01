-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simple_graph_set_has_maximal_member__p2m_e1cd0124_e641_4ece_baff_4e3ebf9bbef8_a1
-- name    : WilliamsonShmoys.finite_simple_graph_set_has_maximal_member__p2m_e1cd0124_e641_4ece_baff_4e3ebf9bbef8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:53:31.554068+00:00
-- url     : https://prove2.me/theorems/024c51b9-7d60-41c4-876a-c60580a29094
-- title:
--   A nonempty set of finite simple graphs has a maximal member
-- statement:
--   For any nonempty set of simple graphs on a finite linearly ordered vertex type, there is a member that has no strictly larger member in that set. The finite order and empty vertex cases are included.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.finite_simple_graph_set_has_maximal_member__p2m_e1cd0124_e641_4ece_baff_4e3ebf9bbef8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (S : Set (SimpleGraph V)) (hS : S.Nonempty) :
    ∃ G : SimpleGraph V, G ∈ S ∧
      ∀ H : SimpleGraph V, H ∈ S → G ≤ H → H ≤ G := by
  sorry
