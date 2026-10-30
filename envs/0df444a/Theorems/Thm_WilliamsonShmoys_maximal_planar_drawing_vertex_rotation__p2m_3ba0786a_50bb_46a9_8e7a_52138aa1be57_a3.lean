-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_vertex_rotation__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
-- name    : WilliamsonShmoys.maximal_planar_drawing_vertex_rotation__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:53:36.662413+00:00
-- url     : https://prove2.me/theorems/e63143a4-1d37-4669-84fc-4ce72e6e836f
-- title:
--   Facial data induces a transitive vertex rotation
-- statement:
--   For the triangular dart data of a maximal drawable graph, the successor that reverses a dart and advances to the next side reaches every dart with the same tail. This is the local cyclic-order property around each vertex.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_vertex_rotation__p2m_3ba0786a_50bb_46a9_8e7a_52138aa1be57_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ M : SimpleGraph V, H ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = H)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f))
    (hCovered : ∀ v, ∃ f i, corner f i = v) :
    ∀ d e : H.Dart, d.fst = e.fst →
      ∃ k : Nat,
        (fun a : H.Dart => dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e := by sorry
