-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:51.617201+00:00
-- url     : https://prove2.me/theorems/0227f8b9-c5e1-4755-9e67-a93be5e3575c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph with at least three vertices that has no proper drawable supergraph on the same vertices has exactly 3|V|−6 edges. A proof route is to show maximality forces connectedness and triangular faces in a planar embedding, then combine the face-degree equation 3F=2E with Euler’s formula V−E+F=2. The boundary hypothesis is retained because the edge formula need not hold for smaller vertex sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V,
      (∀ {u v : V}, Q.Adj u v → R.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn R →
      R = Q) :
    letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
    3 * Fintype.card V = Q.edgeFinset.card + 6 := by sorry
