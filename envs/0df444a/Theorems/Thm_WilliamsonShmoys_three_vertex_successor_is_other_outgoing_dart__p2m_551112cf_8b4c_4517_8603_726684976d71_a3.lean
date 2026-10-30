-- Prove2me | Theorems.Thm_WilliamsonShmoys_three_vertex_successor_is_other_outgoing_dart__p2m_551112cf_8b4c_4517_8603_726684976d71_a3
-- name    : WilliamsonShmoys.three_vertex_successor_is_other_outgoing_dart__p2m_551112cf_8b4c_4517_8603_726684976d71_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:24:33.413709+00:00
-- url     : https://prove2.me/theorems/6505a419-e4ea-46a8-8fe5-bddee39cce23
-- title:
--   Face successor gives a distinct dart with the same tail
-- statement:
--   The face successor defined from the dart equivalence preserves a dart’s tail and is distinct from that dart.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.three_vertex_successor_is_other_outgoing_dart__p2m_551112cf_8b4c_4517_8603_726684976d71_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (F : Type) [Fintype F]
    (corner : F → Fin 3 → V)
    (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : ∀ f, Function.Injective (corner f)) :
    let succ : H.Dart → H.Dart :=
      fun a => dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)
    ∀ d : H.Dart, (succ d).fst = d.fst ∧ succ d ≠ d := by sorry
