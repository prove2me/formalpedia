-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_across_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2
-- name    : WilliamsonShmoys.planar_drawing_add_edge_across_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:57:18.845131+00:00
-- url     : https://prove2.me/theorems/08c93e25-271f-4f67-ba1c-b227be2357fa
-- title:
--   Add a planar bridge across an edge-free cut
-- statement:
--   Given a planar drawing and an edge-free cut separating `a` from `b`, add exactly the edge between them while preserving a planar drawing on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_edge_across_cut__p2m_95b2a4a5_f4af_45e5_83a3_0810e97a8978_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (P : Set V) (a b : V)
    (ha : P a) (hb : ¬ P b)
    (hcut : ∀ u v, K.Adj u v → (P u ↔ P v))
    (hK : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.Adj a b ∧
      ∀ u v, L.Adj u v →
        K.Adj u v ∨ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by sorry
