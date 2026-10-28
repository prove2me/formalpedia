-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_maximal_drawable_supergraph_7f31c9a2
-- name    : WilliamsonShmoys.planar_triangulation_extension_maximal_drawable_supergraph_7f31c9a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:41:16.144362+00:00
-- url     : https://prove2.me/theorems/9506ec0d-58ef-4027-ba20-b6fc6c8aca16
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph is contained in a drawable supergraph on the same vertices that has no drawable strict supergraph. Since there are finitely many simple graphs on V, choose one among the drawable supergraphs of K with maximum edge-set cardinality. A drawable supergraph containing it must then have the same edge set. This removes the finite maximization and maximality-selection step from the parent and does not require the lower bound on |V|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_maximal_drawable_supergraph_7f31c9a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V,
      K.edgeSet ⊆ H.edgeSet ∧
      HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V,
        H.edgeSet ⊆ J.edgeSet → HasPlanarDrawingOn J →
          J.edgeSet = H.edgeSet := by
  sorry
