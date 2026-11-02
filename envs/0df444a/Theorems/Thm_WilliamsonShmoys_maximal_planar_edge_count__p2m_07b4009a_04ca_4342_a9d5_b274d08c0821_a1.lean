-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:39:16.887958+00:00
-- url     : https://prove2.me/theorems/344124b5-d420-40df-b6d0-816baecb63ba
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   If a drawable simple graph on at least three vertices has no drawable strict edge supergraph on those vertices, then it has exactly 3n−6 edges. A proof route is to show maximality forces a connected triangulation, then apply Euler’s formula and count each face boundary edge twice. The n≥3 condition covers the triangle boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    (∀ K : SimpleGraph V,
      H.edgeFinset ⊆ K.edgeFinset →
      HasPlanarDrawingOn K →
      K.edgeFinset ⊆ H.edgeFinset) →
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by
  sorry
