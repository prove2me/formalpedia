-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_ctx816e1e7
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_ctx816e1e7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:13:34.741994+00:00
-- url     : https://prove2.me/theorems/323897c1-63f7-4a6a-b261-150edcd86b65
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on that same vertex type. The finiteness argument ranges over the possible edge sets; it preserves the drawing predicate by selecting a graph from the class of drawable supergraphs, rather than requiring the original drawing to stay fixed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_ctx816e1e7
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      Q ≤ R ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      ∀ S : SimpleGraph V, R ≤ S →
        WilliamsonShmoys.HasPlanarDrawingOn S → S ≤ R := by sorry
