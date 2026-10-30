-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_data__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_data__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:45:09.298699+00:00
-- url     : https://prove2.me/theorems/3ba0786a-50bb-46a9-8e7a-52138aa1be57
-- title:
--   A maximal planar drawing supplies triangular face data
-- statement:
--   A maximal drawable finite simple graph with at least three vertices has finite triangular face data whose sides biject with oriented graph darts, whose endpoints match consecutive corners, and whose corners cover the vertices with transitive rotations. This packages all `TriangularMap` fields other than connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_face_data__p2m_4231ee8f_e4d1_40b7_a8b0_f5da488ab36d_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H) :
    ∃ (F : Type) (instF : Fintype F)
      (corner : F → Fin 3 → V)
      (dart : (F × Fin 3) ≃ H.Dart),
      (∀ f i, (dart (f, i)).fst = corner f i) ∧
      (∀ f i, (dart (f, i)).snd = corner f (i + 1)) ∧
      (∀ f, Function.Injective (corner f)) ∧
      (∀ v, ∃ f i, corner f i = v) ∧
      (∀ d e : H.Dart, d.fst = e.fst →
        ∃ k : Nat,
          (fun a : H.Dart => dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e) := by sorry
