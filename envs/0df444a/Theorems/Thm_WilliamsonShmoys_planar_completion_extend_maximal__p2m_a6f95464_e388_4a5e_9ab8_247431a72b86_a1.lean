-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_extend_maximal__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
-- name    : WilliamsonShmoys.planar_completion_extend_maximal__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:17:05.001346+00:00
-- url     : https://prove2.me/theorems/74a4b7b3-94de-478d-99dc-7f2793476374
-- title:
--   Extend a drawable graph to a maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite fixed vertex set has an inclusion maximal drawable supergraph on that same vertex set. The finite collection of simple graphs on the vertex set permits choosing a maximal drawable extension; the drawing condition is retained as part of the choice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_extend_maximal__p2m_a6f95464_e388_4a5e_9ab8_247431a72b86_a1
    {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      ∀ R : SimpleGraph V, Q ≤ R →
        WilliamsonShmoys.HasPlanarDrawingOn R → R ≤ Q := by sorry
