-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_disconnected_strict_extension__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2
-- name    : WilliamsonShmoys.planar_drawing_disconnected_strict_extension__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:03:44.098771+00:00
-- url     : https://prove2.me/theorems/1532c25a-65bb-404f-a90f-83fae1a22778
-- title:
--   Strict planar extension of a disconnected drawing
-- statement:
--   A disconnected graph with a crossing-free drawing and at least three vertices has a strictly larger planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_disconnected_strict_extension__p2m_a61b4d52_11af_49e1_8b44_bf89679ad338_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) (hdisc : ¬ G.Connected) : ∃ H : SimpleGraph V, G < H ∧ HasPlanarDrawingOn H := by sorry
