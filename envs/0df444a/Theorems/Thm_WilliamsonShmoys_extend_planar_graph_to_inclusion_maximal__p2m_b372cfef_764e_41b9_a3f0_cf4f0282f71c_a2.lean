-- Prove2me | Theorems.Thm_WilliamsonShmoys_extend_planar_graph_to_inclusion_maximal__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2
-- name    : WilliamsonShmoys_extend_planar_graph_to_inclusion_maximal__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:15.789878+00:00
-- url     : https://prove2.me/theorems/655608fd-9cc4-4697-9d54-637a0388a99e
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph that has no drawable strict supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_extend_planar_graph_to_inclusion_maximal__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    Exists fun (L : SimpleGraph V) => Exists fun (dL : DecidableRel L.Adj) =>
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      G.edgeFinset ⊆ L.edgeFinset ∧
      (∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn H →
        L.edgeFinset ⊆ H.edgeFinset → H.edgeFinset = L.edgeFinset) := by
  sorry
