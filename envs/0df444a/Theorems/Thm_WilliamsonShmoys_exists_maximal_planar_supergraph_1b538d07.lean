-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_1b538d07
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_1b538d07
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:06:08.464802+00:00
-- url     : https://prove2.me/theorems/2808338a-06f1-43b5-8128-322e6655efba
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable supergraph with no strictly larger drawable supergraph on that type. Maximize edge count over the finite family of drawable supergraphs containing `J`; this family contains `J`, and a strict extension has more edges. The argument removes the existence and maximality step from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_1b538d07
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ K : SimpleGraph V,
      J ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → K ≠ L →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
