-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_gives_face_data
-- name    : WilliamsonShmoys.planar_drawing_on_gives_face_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:59:30.19933+00:00
-- url     : https://prove2.me/theorems/010edba0-f1b8-47c9-83eb-665cf50b5410
-- title:
--   A connected plane drawing yields Euler and face-side counts
-- statement:
--   For a connected finite simple graph on at least three vertices, a crossing-free arc drawing induces a finite face count satisfying Euler's formula and the summed lower bound of three edge-sides per face, counting repeated sides with multiplicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_on_gives_face_data
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hConn : forall u v, Relation.ReflTransGen J.Adj u v)
    (hV : 3 <= Fintype.card V)
    (hJ : WilliamsonShmoys.HasPlanarDrawingOn J) :
    ∃ F : ℕ, Fintype.card V + F = J.edgeSet.ncard + 2 ∧
      3 * F <= 2 * J.edgeSet.ncard := by sorry
