-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2
-- name    : WilliamsonShmoys_maximal_planar_graph_connected__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:29:09.465226+00:00
-- url     : https://prove2.me/theorems/2260a117-6439-491e-b3cc-351c9a5eff37
-- title:
--   An inclusion-maximal planar graph is connected
-- statement:
--   A planar graph on at least three vertices that has no strictly larger planar supergraph on the same vertices is connected. If it were disconnected, an arc in the unbounded face could join exposed vertices of distinct components and give a larger planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_maximal_planar_graph_connected__p2m_f305e987_8fa4_48f1_bb88_04ada6b91b35_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.Connected := by
  sorry
