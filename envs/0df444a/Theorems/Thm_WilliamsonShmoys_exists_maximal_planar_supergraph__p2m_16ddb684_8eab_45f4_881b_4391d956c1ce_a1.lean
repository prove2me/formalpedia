-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T07:21:38.527465+00:00
-- url     : https://prove2.me/theorems/ff12c35c-458d-4332-a272-1b92553a498b
-- title:
--   Choose a maximal drawable supergraph on a finite vertex type
-- statement:
--   On a finite ordered vertex type, extend any drawable graph to a drawable graph maximal under drawable supergraph inclusion. There are finitely many simple graphs; choose one with the greatest edge count among drawable supergraphs of the input. Inclusion and equality of finite edge counts establish maximality, without a lower bound on the vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_16ddb684_8eab_45f4_881b_4391d956c1ce_a1
    {α : Type} [Fintype α] [LinearOrder α]
    (G : SimpleGraph α)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ M : SimpleGraph α,
      G.edgeSet.ncard ≤ M.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      (∀ N : SimpleGraph α, M ≤ N →
        WilliamsonShmoys.HasPlanarDrawingOn N → N = M) := by sorry
