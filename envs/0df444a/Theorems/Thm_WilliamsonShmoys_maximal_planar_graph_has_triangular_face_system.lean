-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_triangular_face_system
-- name    : WilliamsonShmoys.maximal_planar_graph_has_triangular_face_system
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T07:18:27.595931+00:00
-- url     : https://prove2.me/theorems/dbe31774-754a-438d-8899-035a30921612
-- title:
--   Face system of an edge-maximal planar graph
-- statement:
--   An edge-maximal planar graph with at least three vertices admits a multiset of triangular faces in which each graph edge belongs to exactly two faces and the Euler equation holds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_has_triangular_face_system
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H <= K → K ≠ H →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn K) :
    WilliamsonShmoys.HasTriangularPlaneFaceSystem H := by sorry
