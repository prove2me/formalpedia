-- Prove2me | Theorems.Thm_WilliamsonShmoys_four_vertex_triangular_rotation_transitive__p2m_a3a0a250_04a2_4577_b872_e6afd6b9d768_a1
-- name    : WilliamsonShmoys.four_vertex_triangular_rotation_transitive__p2m_a3a0a250_04a2_4577_b872_e6afd6b9d768_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:26:42.324795+00:00
-- url     : https://prove2.me/theorems/d0b65569-8792-429c-bbc9-f16b6065a44f
-- title:
--   Triangular dart data gives transitive local rotation on four vertices
-- statement:
--   For complete four-vertex graph dart data satisfying the triangular corner and bijection conditions, every fixed-tail dart fiber is transitive under the induced local successor.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.four_vertex_triangular_rotation_transitive__p2m_a3a0a250_04a2_4577_b872_e6afd6b9d768_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : Fintype.card V = 4)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f))
    (hCovered : ∀ v, ∃ f i, corner f i = v)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v) :
    ∀ d e : H.Dart, d.fst = e.fst →
      ∃ k : Nat,
        (fun a : H.Dart =>
          dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1))^[k] d = e := by sorry
