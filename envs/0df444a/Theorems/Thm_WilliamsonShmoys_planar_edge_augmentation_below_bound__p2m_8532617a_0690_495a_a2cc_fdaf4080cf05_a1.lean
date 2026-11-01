-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:38:43.975206+00:00
-- url     : https://prove2.me/theorems/b501a266-2ceb-4b60-9d31-7e031b204a4c
-- title:
--   Planar edge augmentation below the triangulation bound
-- statement:
--   If a finite planar graph on at least three vertices has fewer than 3|V|−6 edges, it has a planar supergraph on the same vertices with at least one added edge. A proof route is to connect components through faces, then add a diagonal in any face whose boundary is not triangular; if no addition is possible, the resulting triangulation and Euler's formula force the edge count to be 3|V|−6. This removes the maximality-to-lower-bound step from the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_8532617a_0690_495a_a2cc_fdaf4080cf05_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hcard : 3 ≤ Fintype.card V)
    (hsmall : T.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ U : SimpleGraph V,
      T.edgeSet ⊆ U.edgeSet ∧
      ∃ e, e ∈ U.edgeSet ∧ e ∉ T.edgeSet ∧
        WilliamsonShmoys.HasPlanarDrawingOn U := by
  sorry
