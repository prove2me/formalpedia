-- Prove2me | Theorems.Thm_WilliamsonShmoys_localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- name    : WilliamsonShmoys.localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-31T20:57:47.766988+00:00
-- url     : https://prove2.me/theorems/3c2bdd7c-44e5-4568-842a-4cf11f68408d
-- title:
--   Triangular dart successor has no fixed points
-- statement:
--   A fixed point would imply that a `Fin 3` index equals its cyclic successor after applying the inverse equivalence, which is impossible. This supplies the fixed-point-free condition for the parent’s orbit argument.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.localSuccessor_ne_self__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
    {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
    (dart : (F × Fin 3) ≃ H.Dart) (a : H.Dart) :
    (fun a : H.Dart =>
      dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)) a ≠ a := by
  sorry
