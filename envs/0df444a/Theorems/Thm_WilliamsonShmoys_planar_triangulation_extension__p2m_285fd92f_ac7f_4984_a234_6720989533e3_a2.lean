-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_285fd92f_ac7f_4984_a234_6720989533e3_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_285fd92f_ac7f_4984_a234_6720989533e3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:47:46.539915+00:00
-- url     : https://prove2.me/theorems/89a3e2c0-b2b3-4ebc-a282-9a392a489cfc
-- title:
--   Planar triangulation extension with exact edge count
-- statement:
--   Any finite simple graph on an ordered vertex type with at least three vertices that has a crossing-free drawing by arcs has a planar supergraph on the same vertex type with exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_285fd92f_ac7f_4984_a234_6720989533e3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
        (letI : DecidableRel K.Adj := Classical.decRel K.Adj;
         3 * Fintype.card V = K.edgeFinset.card + 6) := by sorry
