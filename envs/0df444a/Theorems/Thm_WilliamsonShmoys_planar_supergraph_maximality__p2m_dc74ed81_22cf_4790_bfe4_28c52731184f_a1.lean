-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximality__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximality__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T11:58:33.296701+00:00
-- url     : https://prove2.me/theorems/5b9937cd-fa61-45ce-b5bc-eda05b820748
-- title:
--   Finite maximal planar supergraph extension
-- statement:
--   Every planar drawing on a finite ordered vertex type has a planar supergraph on the same vertices whose edge set is inclusion-maximal among planar supergraphs. This removes the selection and maximality step from the parent. A proof route is to consider the finite set of edge sets of planar supergraphs containing H and choose one of maximum cardinality; a strict planar supergraph would contradict that choice. The drawing predicate is preserved by the choice because each candidate is required to have its own drawing. No lower bound on the number of vertices is needed for this extension step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximality__p2m_dc74ed81_22cf_4790_bfe4_28c52731184f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet ⊆ K.edgeSet ∧
      ∀ L : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeSet ⊆ L.edgeSet →
        L.edgeSet ⊆ K.edgeSet := by sorry
