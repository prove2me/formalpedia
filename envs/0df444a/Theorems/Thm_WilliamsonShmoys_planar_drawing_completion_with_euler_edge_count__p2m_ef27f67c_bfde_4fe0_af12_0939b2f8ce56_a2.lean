-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_completion_with_euler_edge_count__p2m_ef27f67c_bfde_4fe0_af12_0939b2f8ce56_a2
-- name    : WilliamsonShmoys_planar_drawing_completion_with_euler_edge_count__p2m_ef27f67c_bfde_4fe0_af12_0939b2f8ce56_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:01:38.819196+00:00
-- url     : https://prove2.me/theorems/b372cfef-764e-41b9-a3f0-cf4f0282f71c
-- title:
--   Complete a drawable graph to a maximal planar supergraph with Euler edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices is contained in a drawable simple graph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_planar_drawing_completion_with_euler_edge_count__p2m_ef27f67c_bfde_4fe0_af12_0939b2f8ce56_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    Exists fun (L : SimpleGraph V) => Exists fun (dL : DecidableRel L.Adj) =>
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      G.edgeFinset ⊆ L.edgeFinset ∧
      L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
