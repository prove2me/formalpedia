-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_supergraph_exists__p2m_10f04ae6_54c9_4ed6_b5cd_b1cd1816504e_a1
-- name    : WilliamsonShmoys.planar_connected_supergraph_exists__p2m_10f04ae6_54c9_4ed6_b5cd_b1cd1816504e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:37:25.039514+00:00
-- url     : https://prove2.me/theorems/b3fecde6-4daa-4e86-a54a-c39dae3adc36
-- title:
--   Extend a nontrivial planar graph to a connected planar supergraph
-- statement:
--   Any graph on at least three vertices with a crossing-free drawing has a connected supergraph on the same vertices that also has a crossing-free drawing. This strengthens the target’s strict-extension conclusion and isolates the geometric task of connecting components while preserving a drawing. The cardinality hypothesis rules out the empty-vertex boundary case flagged in earlier related work. A proof route is to normalize a finite planar embedding, then add noncrossing edges through faces until the components are connected, checking the arc and intersection requirements of `HasPlanarDrawingOn`. The remaining core obligation is to formalize that normalization and edge-insertion construction for the explicit arc-based definition; no existing proof source for that exact construction was verified.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_supergraph_exists__p2m_10f04ae6_54c9_4ed6_b5cd_b1cd1816504e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
