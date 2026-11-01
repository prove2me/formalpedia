-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_finite_extension__p2m_c129c456_fb95_4993_b973_699ff9e1cc14_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_finite_extension__p2m_c129c456_fb95_4993_b973_699ff9e1cc14_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:24:51.309439+00:00
-- url     : https://prove2.me/theorems/10426469-5473-4182-becf-e13672db16ef
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For any finite vertex type, graph H, and graph property P satisfied by H, there is a supergraph K satisfying P that is maximal among P supergraphs of H; K has at least as many edges as H.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_finite_extension__p2m_c129c456_fb95_4993_b973_699ff9e1cc14_a1
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hP : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      P K ∧
      (∀ L : SimpleGraph V, K ≤ L → P L → L ≤ K) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
