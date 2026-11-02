-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:50:11.307116+00:00
-- url     : https://prove2.me/theorems/8a171377-f33b-49cc-b27f-3a0a7f3acd0d
-- title:
--   An inclusion-maximal planar graph has the triangulation edge count
-- statement:
--   A finite inclusion-maximal planar simple graph with at least three vertices has exactly 3|V|−6 edges. The proof route is to use maximality to establish connectedness and triangular faces in a plane embedding, then apply Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_8e688b5a_4cd6_4a71_af1c_8dd5b2ac94c3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 ≤ Fintype.card V)
    (hmax : ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeFinset ⊆ L.edgeFinset → K.edgeFinset = L.edgeFinset) :
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
