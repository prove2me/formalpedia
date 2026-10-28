-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_from_finite_component_partition
-- name    : WilliamsonShmoys.planar_edge_bound_from_finite_component_partition
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:31:36.268923+00:00
-- url     : https://prove2.me/theorems/15036e62-a294-4145-9dc7-fe9b5ca471f1
-- title:
--   Aggregate connected component edge bounds
-- statement:
--   For a finite partition into nonempty sets with connected induced subgraphs, if vertex counts and edge counts add across the partition and each component of size at least three satisfies the six-unit edge bound, then the whole graph satisfies that bound whenever it has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_bound_from_finite_component_partition
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (comps : Finset (Set V))
    (hne : ∀ C ∈ comps, C.Nonempty)
    (hconnected : ∀ C ∈ comps, (K.induce C).Connected)
    (hcard : ∑ C ∈ comps, C.ncard = Fintype.card V)
    (hedge : K.edgeSet.ncard = ∑ C ∈ comps, (K.induce C).edgeSet.ncard)
    (hconn : ∀ (W : Set V) [Fintype W],
      3 ≤ Fintype.card W →
      (K.induce W).Connected →
      (K.induce W).edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
