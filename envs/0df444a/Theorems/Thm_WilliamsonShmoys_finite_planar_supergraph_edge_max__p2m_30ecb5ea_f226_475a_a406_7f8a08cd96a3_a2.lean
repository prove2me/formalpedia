-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_planar_supergraph_edge_max__p2m_30ecb5ea_f226_475a_a406_7f8a08cd96a3_a2
-- name    : WilliamsonShmoys.finite_planar_supergraph_edge_max__p2m_30ecb5ea_f226_475a_a406_7f8a08cd96a3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:15:08.823338+00:00
-- url     : https://prove2.me/theorems/3c3d2660-b556-4bc4-b33e-3667aa2b5b2f
-- title:
--   Finite edge-maximal drawable supergraph
-- statement:
--   Among drawable supergraphs of K, there is one whose edge-set cardinality is at least that of every other drawable supergraph. This removes the finite optimization step from the parent. Its independent proof route is to maximize edgeSet.ncard over the finite collection of graphs on V satisfying both supergraph and drawing conditions; K itself proves that collection is nonempty. The drawing predicate is only used to filter candidates. The remaining core obligation is to formalize this finite maximum in Lean.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.finite_planar_supergraph_edge_max__p2m_30ecb5ea_f226_475a_a406_7f8a08cd96a3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (L : SimpleGraph V), K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∀ (M : SimpleGraph V), K ≤ M →
        WilliamsonShmoys.HasPlanarDrawingOn M →
          M.edgeSet.ncard ≤ L.edgeSet.ncard := by sorry
