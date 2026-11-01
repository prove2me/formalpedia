-- Prove2me | Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_graph_has_euler_edge_count__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2
-- name    : WilliamsonShmoys_inclusion_maximal_planar_graph_has_euler_edge_count__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:13:19.420923+00:00
-- url     : https://prove2.me/theorems/47c18254-8e9b-4a76-b436-1915ac92f140
-- title:
--   An inclusion-maximal drawable graph has the Euler edge count
-- statement:
--   An inclusion-maximal drawable graph on at least three finite ordered vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys_inclusion_maximal_planar_graph_has_euler_edge_count__p2m_b372cfef_764e_41b9_a3f0_cf4f0282f71c_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn H →
      L.edgeFinset ⊆ H.edgeFinset → H.edgeFinset = L.edgeFinset) :
    L.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
