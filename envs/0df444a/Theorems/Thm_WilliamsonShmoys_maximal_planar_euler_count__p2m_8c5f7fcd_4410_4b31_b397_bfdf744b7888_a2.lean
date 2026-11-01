-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
-- name    : WilliamsonShmoys.maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:22:51.742489+00:00
-- url     : https://prove2.me/theorems/1fae8d59-e553-43b6-adc4-9f2b440ae2bb
-- title:
--   Euler edge count for a maximal drawable graph
-- statement:
--   An inclusion-maximal graph with the supplied crossing-free drawing and at least three vertices has exactly `3 * card V - 6` edges, expressed as `edgeFinset.card + 6 = 3 * card V`. A proof can complete the drawing to a plane triangulation, establish Euler’s formula and count edge-face incidences. This removes the geometric counting obligation from the parent; formalizing those facts from the arc predicates remains the core work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_euler_count__p2m_8c5f7fcd_4410_4b31_b397_bfdf744b7888_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall K' : SimpleGraph V, H <= K' -> WilliamsonShmoys.HasPlanarDrawingOn K' -> K' = H)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by sorry
