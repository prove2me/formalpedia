-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_extension_of_disconnected__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
-- name    : WilliamsonShmoys.planar_drawing_strict_extension_of_disconnected__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:19:59.912391+00:00
-- url     : https://prove2.me/theorems/10f04ae6-54c9-4ed6-b5cd-b1cd1816504e
-- title:
--   A disconnected planar drawing with at least three vertices admits a strict planar extension
-- statement:
--   For a finite linearly ordered vertex type with at least three vertices, a disconnected graph with a crossing-free drawing has a strictly larger graph on the same vertices that also has a crossing-free drawing. The cardinality hypothesis is retained from the parent to rule out the empty-vertex boundary case. A proof must construct a connecting edge in the embedding and verify that its arc avoids all vertices in its interior and meets existing edges only at permitted endpoints. The remaining core obligation is this geometric construction; the research notes flag related attempts but supply no source-level counterexample to this bounded statement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_strict_extension_of_disconnected__p2m_120b8d49_099c_4729_927b_decab250b8ce_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H < K ∧ HasPlanarDrawingOn K := by
  sorry
