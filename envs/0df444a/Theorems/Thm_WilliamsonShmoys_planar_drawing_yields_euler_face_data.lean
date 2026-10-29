-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_yields_euler_face_data
-- name    : WilliamsonShmoys.planar_drawing_yields_euler_face_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:03:38.718866+00:00
-- url     : https://prove2.me/theorems/3dc70f40-f8da-4d4c-98d1-32c92197df22
-- title:
--   A drawing with at least two edges yields Euler face data
-- statement:
--   For a finite simple graph with at least three vertices, a drawing witnessed by `HasPlanarDrawingOn`, and at least two edges, produce natural-number face and component counts satisfying Euler’s relation and the aggregate face-degree inequality. The component count must include isolated vertices; the edge lower bound excludes the edgeless and single-edge face-degree exceptions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_yields_euler_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hm : 2 ≤ L.edgeSet.ncard) :
    ∃ (f c : ℕ),
      Fintype.card V + f = L.edgeSet.ncard + c + 1 ∧
      1 ≤ c ∧
      3 * f ≤ 2 * L.edgeSet.ncard := by sorry
