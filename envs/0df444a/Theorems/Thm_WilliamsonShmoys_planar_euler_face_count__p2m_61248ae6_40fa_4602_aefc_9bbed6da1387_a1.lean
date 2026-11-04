-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_face_count__p2m_61248ae6_40fa_4602_aefc_9bbed6da1387_a1
-- name    : WilliamsonShmoys.planar_euler_face_count__p2m_61248ae6_40fa_4602_aefc_9bbed6da1387_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:45:25.60729+00:00
-- url     : https://prove2.me/theorems/13cac36b-d337-49ef-981f-d43d139f211c
-- title:
--   Euler face count and incidence bound for a planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing as defined by WilliamsonShmoys.HasPlanarDrawingOn, there is a natural number of faces f satisfying Euler’s formula and the bound obtained by counting at least three edge incidences on each face. This isolates the geometric and combinatorial core; the parent theorem follows from these two inequalities.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_euler_face_count__p2m_61248ae6_40fa_4602_aefc_9bbed6da1387_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hV : 3 ≤ Fintype.card V)
    (hconn : K.Connected)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * K.edgeFinset.card := by sorry
