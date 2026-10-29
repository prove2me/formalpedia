-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4
-- name    : WilliamsonShmoys.planar_connected_supergraph_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T05:13:39.809316+00:00
-- url     : https://prove2.me/theorems/d5ec0378-40af-49f0-96a5-235e13fa397b
-- title:
--   Connected planar supergraph on the same vertices
-- statement:
--   Extend a finite graph with a crossing-free drawing to a connected graph on the same vertices, retaining a crossing-free drawing and at least as many edges. This isolates the task of joining distinct drawn components by arcs in the complement of the finite drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_supergraph_repair__p2m_21446003_fac0_46fd_be6f_03d17c7cc1aa_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U) :
    ∃ H : SimpleGraph V,
      U.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v, Relation.ReflTransGen H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
