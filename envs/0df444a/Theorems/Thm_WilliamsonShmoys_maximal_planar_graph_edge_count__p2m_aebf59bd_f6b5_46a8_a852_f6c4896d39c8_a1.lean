-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:18:56.568064+00:00
-- url     : https://prove2.me/theorems/694a8160-ff76-4855-a03b-16e16dbb37d5
-- title:
--   A maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly 3|V|−6 edges. This isolates the geometric and Euler-counting work from the parent and the finite maximality argument. A proof route is to show saturation forces connectedness and triangular faces, then count edge-face incidences and use Euler’s formula; the lower boundary |V|=3 is included. This topological argument is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_aebf59bd_f6b5_46a8_a852_f6c4896d39c8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V,
      (∀ ⦃u v : V⦄, K.Adj u v → L.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    (letI : DecidableRel K.Adj := Classical.decRel K.Adj
     K.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
