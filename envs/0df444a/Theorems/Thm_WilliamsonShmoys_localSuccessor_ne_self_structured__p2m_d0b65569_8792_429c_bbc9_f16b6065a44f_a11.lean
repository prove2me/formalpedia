-- Prove2me | Theorems.Thm_WilliamsonShmoys_localSuccessor_ne_self_structured__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a11
-- name    : WilliamsonShmoys.localSuccessor_ne_self_structured__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a11
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:18:43.889802+00:00
-- url     : https://prove2.me/theorems/99f46e07-3c22-498e-afb5-9101a340be04
-- title:
--   Triangular face data rules out a fixed point of the local successor
-- statement:
--   Under the triangular corner endpoint laws, with each face’s three corners injective, the local successor cannot fix any dart. The proof decodes the reversed dart and the dart itself, uses a hypothetical fixed point to relate their face indices, and derives equality of two distinct corners of one face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.localSuccessor_ne_self_structured__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a11
    {V : Type} [Fintype V] {F : Type} [Fintype F]
    {H : SimpleGraph V}
    (corner : F -> Fin 3 -> V)
    (dart : Equiv (Prod F (Fin 3)) H.Dart)
    (hTail : forall f i, (dart (f, i)).fst = corner f i)
    (hHead : forall f i, (dart (f, i)).snd = corner f (i + 1))
    (hInjective : forall f, Function.Injective (corner f))
    (a : H.Dart) :
    Not (dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1) = a) := by sorry
