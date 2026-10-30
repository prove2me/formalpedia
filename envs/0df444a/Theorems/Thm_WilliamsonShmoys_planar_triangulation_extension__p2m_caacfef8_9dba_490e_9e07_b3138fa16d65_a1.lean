-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_caacfef8_9dba_490e_9e07_b3138fa16d65_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_caacfef8_9dba_490e_9e07_b3138fa16d65_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:30:53.491553+00:00
-- url     : https://prove2.me/theorems/ffd3f69d-18cc-4be0-84fa-2bff696b22a9
-- title:
--   Triangulation extension of a finite planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertices with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_caacfef8_9dba_490e_9e07_b3138fa16d65_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, M ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
        H.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
