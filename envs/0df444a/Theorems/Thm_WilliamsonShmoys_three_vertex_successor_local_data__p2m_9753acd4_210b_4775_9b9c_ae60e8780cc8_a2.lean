-- Prove2me | Theorems.Thm_WilliamsonShmoys_three_vertex_successor_local_data__p2m_9753acd4_210b_4775_9b9c_ae60e8780cc8_a2
-- name    : WilliamsonShmoys.three_vertex_successor_local_data__p2m_9753acd4_210b_4775_9b9c_ae60e8780cc8_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:15:53.184547+00:00
-- url     : https://prove2.me/theorems/551112cf-8b4c-4517-8603-726684976d71
-- title:
--   A one-step description of each three-vertex dart fiber
-- statement:
--   For the successor induced by the face rotation, any two darts with the same tail are equal or the second is the successor of the first.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.three_vertex_successor_local_data__p2m_9753acd4_210b_4775_9b9c_ae60e8780cc8_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : Fintype.card V = 3)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f))
    (hCovered : ∀ v, ∃ f i, corner f i = v)
    (hcomplete : ∀ u v : V, u ≠ v → H.Adj u v) :
    let succ : H.Dart → H.Dart := fun a =>
      dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)
    ∀ d e : H.Dart, d.fst = e.fst → d = e ∨ succ d = e := by sorry
