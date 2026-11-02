-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeMaximalPlanar_edgeCount_lower__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
-- name    : WilliamsonShmoys.edgeMaximalPlanar_edgeCount_lower__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:57.703931+00:00
-- url     : https://prove2.me/theorems/07c9f31b-494b-4180-969f-c152b9627c5e
-- title:
--   Maximal connected drawable graphs meet the planar edge bound
-- statement:
--   A connected edge-maximal drawable simple graph on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.edgeMaximalPlanar_edgeCount_lower__p2m_4c527512_1622_4d01_a868_d6bc284410d2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H = K)
    (hconn : K.Connected)
    (hn : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ K.edgeFinset.card := by sorry
