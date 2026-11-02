-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:47:01.255544+00:00
-- url     : https://prove2.me/theorems/0a96650e-3562-4e4d-ac7d-bc404fba85ef
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite ordered vertex type with at least three vertices has exactly 3|V|−6 edges. This isolates the drawing and Euler-count argument from the finite extension step. A proof route is to obtain a plane embedding from the arc drawing, show maximality forces connectedness and triangular faces (including the three-vertex boundary case), then use Euler’s formula and count each face-edge incidence twice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_b6e1b838_6a07_4127_97a1_2301fa6a9ddd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
