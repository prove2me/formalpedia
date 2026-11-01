-- Prove2me | Theorems.Thm_WilliamsonShmoys_localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a9
-- name    : WilliamsonShmoys.localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a9
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T21:28:03.540249+00:00
-- url     : https://prove2.me/theorems/189dd414-c4a9-4e46-b847-ab42bf1587ec
-- title:
--   Triangular dart successor has no fixed points
-- statement:
--   The successor cannot fix a dart because applying the inverse dart equivalence to a fixed-point equality would make a `Fin 3` index equal its cyclic successor. This removes the no-fixed-point calculation from the parent. Prove it by simplifying the equivalence and dart involution, then show addition by one on `Fin 3` has no fixed point. The argument needs no completeness or vertex-count hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a9
    {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
    (dart : Equiv (Prod F (Fin 3)) H.Dart) (a : H.Dart) :
    Not ((fun a : H.Dart =>
      dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)) a = a) := by sorry
