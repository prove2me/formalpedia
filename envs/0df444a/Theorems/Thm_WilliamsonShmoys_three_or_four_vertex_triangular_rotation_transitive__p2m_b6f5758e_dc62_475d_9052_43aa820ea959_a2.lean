-- Prove2me | Theorems.Thm_WilliamsonShmoys_three_or_four_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
-- name    : WilliamsonShmoys.three_or_four_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:20:47.329232+00:00
-- url     : https://prove2.me/theorems/a3a0a250-04a2-4577-b872-e6afd6b9d768
-- title:
--   Triangular dart data gives transitive local rotation on three or four vertices
-- statement:
--   When the complete graph has three or four vertices, the supplied bijective triangular dart data makes every fixed-tail dart set a single cycle under the induced successor.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Theorems.Thm_WilliamsonShmoys_three_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.three_or_four_vertex_triangular_rotation_transitive__p2m_b6f5758e_dc62_475d_9052_43aa820ea959_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hVlo : 3 ≤ Fintype.card V)
    (hVhi : Fintype.card V ≤ 4)
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
