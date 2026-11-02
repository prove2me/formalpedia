-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_disconnected_strict_extension__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
-- name    : WilliamsonShmoys.planar_disconnected_strict_extension__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:59:56.113984+00:00
-- url     : https://prove2.me/theorems/583909d6-9a92-4051-aa1a-1f45dfd3ea8e
-- title:
--   A disconnected planar drawing admits a strict planar extension
-- statement:
--   A disconnected finite graph with a crossing-free drawing and at least three vertices has a strictly larger planar supergraph on the same vertex set. The intended route is to join components by an arc in the complement of the finite drawing, maintaining the drawing’s endpoint, injectivity, and nonintersection conditions. This isolates the topological work needed by the parent; the maximality lemma and the parent derivation do not prove that geometric step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_disconnected_strict_extension__p2m_8e16201b_1194_4bde_8c0d_f203800a8dc6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hDisconnected : ¬ H.Connected)
    (hn : Nat.le 3 (Fintype.card V)) :
    Exists fun (J : SimpleGraph V) =>
      Exists fun (dJ : DecidableRel J.Adj) =>
        And (H ≤ J)
          (And (H ≠ J) (WilliamsonShmoys.HasPlanarDrawingOn J)) := by
  sorry
