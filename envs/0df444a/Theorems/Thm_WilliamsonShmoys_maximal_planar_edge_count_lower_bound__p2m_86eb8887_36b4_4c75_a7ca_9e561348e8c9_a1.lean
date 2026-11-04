-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:34:35.444453+00:00
-- url     : https://prove2.me/theorems/924b9ea4-0b38-4572-b493-5a5eee48f103
-- title:
--   Maximal planar graph edge-count lower bound
-- statement:
--   If a drawable simple graph on at least three vertices cannot be extended by adding edges while retaining a planar drawing, it has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_86eb8887_36b4_4c75_a7ca_9e561348e8c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K) :
    letI : ∀ L : SimpleGraph V, DecidableRel L.Adj :=
      fun L => Classical.decRel L.Adj
    (∀ L : SimpleGraph V,
      K.edgeFinset ⊆ L.edgeFinset →
      HasPlanarDrawingOn L →
      L.edgeFinset = K.edgeFinset) →
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by sorry
