-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_map__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_triangular_map__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:33:01.018531+00:00
-- url     : https://prove2.me/theorems/4231ee8f-e4d1-40b7-a8b0-f5da488ab36d
-- title:
--   A maximal planar drawing induces a triangular map
-- statement:
--   Every inclusion-maximal drawable finite simple graph on at least three vertices admits a finite oriented triangular map with the dart correspondence, corner properties, vertex coverage, and transitive vertex rotations required by the existing structure.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_triangular_map__p2m_fe860f1c_6599_42e8_850c_50d6abf755f9_a12
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H) :
    ∃ (F : Type) (instF : Fintype F),
      Nonempty (@WilliamsonShmoys.TriangularMap V ‹Fintype V› H F instF) := by sorry
