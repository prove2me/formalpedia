-- Prove2me | Theorems.Thm_WilliamsonShmoys_localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
-- name    : WilliamsonShmoys.localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:17:09.430103+00:00
-- url     : https://prove2.me/theorems/53d1fca3-6b5f-4487-8df0-e2b9379e6c74
-- title:
--   Triangular dart successor has no fixed points
-- statement:
--   A fixed point would force a `Fin 3` index to equal its cyclic successor after applying the inverse dart equivalence and canceling dart reversal. This isolates fixed-point exclusion. Prove it by applying the inverse equivalence to the alleged equality and using that adding one modulo three has no fixed point.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a8
    {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
    (dart : Equiv (Prod F (Fin 3)) H.Dart) (a : H.Dart) :
    Not ((fun a : H.Dart =>
      dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)) a = a) := by sorry
