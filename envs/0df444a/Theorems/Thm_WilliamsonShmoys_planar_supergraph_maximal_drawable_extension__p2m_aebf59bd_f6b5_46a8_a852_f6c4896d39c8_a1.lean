-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_drawable_extension__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal_drawable_extension__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:18:55.35039+00:00
-- url     : https://prove2.me/theorems/5ebc579d-e867-4b37-8c7c-74706e0b98a2
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on the same vertices that is maximal under drawable supergraph inclusion. This removes the finite-choice and maximality step from the parent; choose a drawable supergraph with maximum edge count among the finitely many simple graphs on V. The hcard hypothesis is retained for compatibility with the parent, though this existence argument does not need it. The remaining obligation is the topological edge-count result for such a maximal graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal_drawable_extension__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L → L = K) := by sorry
