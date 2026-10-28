-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph_a8cccb55
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph_a8cccb55
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T13:30:58.852307+00:00
-- url     : https://prove2.me/theorems/d5fc4b0a-bf90-4945-9431-9c02fb482d6c
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on the given finite vertex type is contained in a drawable supergraph that is maximal among drawable graphs on that same type. The proof route is to use finiteness of the set of simple graphs on the vertex type, restrict to drawable supergraphs of W, and select one with the largest edge set. This removes the finite maximal-extension step from the parent. The boundary case of three vertices is covered: the candidate family contains W and is finite. The remaining obligation is to formalize finiteness and maximality for the packaged drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph_a8cccb55
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ U : SimpleGraph V,
      W ≤ U ∧
      WilliamsonShmoys.HasPlanarDrawingOn U ∧
      ∀ X : SimpleGraph V,
        U ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = U := by sorry
