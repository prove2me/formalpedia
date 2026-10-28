-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_triangulation_289ce3bb
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension_triangulation_289ce3bb
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T14:36:51.451461+00:00
-- url     : https://prove2.me/theorems/64d44347-8d29-4e9a-9581-603cf3eb0240
-- title:
--   Extend a planar drawing to a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set that is maximal among drawable supergraphs and has at least as many edges. One proof route is to select a maximum-edge member of the finite nonempty family of drawable supergraphs containing the input graph; this must be formalized for the packaged drawing predicate, including disconnected inputs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension_triangulation_289ce3bb
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ K : SimpleGraph V, N ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = N) ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard := by sorry
