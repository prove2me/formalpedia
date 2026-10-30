-- Prove2me | Theorems.Thm_WilliamsonShmoys_localSuccessor_tail__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5
-- name    : WilliamsonShmoys.localSuccessor_tail__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:46:26.752459+00:00
-- url     : https://prove2.me/theorems/1674a10a-7413-464c-95a7-ca7e73c084c5
-- title:
--   Triangular dart successor preserves its tail
-- statement:
--   The original dart's head is the next corner of its face, which is the successor dart's tail by the supplied corner equations. This removes tail preservation from the parent; it does not need completeness, coverage, or the vertex count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.localSuccessor_tail__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a5
    {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
    (corner : F → Fin 3 → V) (dart : (F × Fin 3) ≃ H.Dart)
    (hTail : ∀ f i, (dart (f, i)).fst = corner f i)
    (hHead : ∀ f i, (dart (f, i)).snd = corner f (i + 1))
    (a : H.Dart) :
    (dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)).fst = a.fst := by
  sorry
