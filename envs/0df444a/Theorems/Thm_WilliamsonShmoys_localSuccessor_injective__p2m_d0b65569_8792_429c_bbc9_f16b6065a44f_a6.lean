-- Prove2me | Theorems.Thm_WilliamsonShmoys_localSuccessor_injective__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- name    : WilliamsonShmoys.localSuccessor_injective__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:57:46.803014+00:00
-- url     : https://prove2.me/theorems/301dfd88-1ad9-4d38-853e-110aa7bd5eba
-- title:
--   Triangular dart successor is injective
-- statement:
--   The successor is a composition of dart reversal, the dart equivalence and its inverse, and cyclic index increment on `Fin 3`. These operations are bijective, so this child supplies the parent’s injectivity hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.localSuccessor_injective__p2m_d0b65569_8792_429c_bbc9_f16b6065a44f_a6
    {V : Type} [Fintype V] {F : Type} [Fintype F] {H : SimpleGraph V}
    (dart : (F × Fin 3) ≃ H.Dart) :
    Function.Injective (fun a : H.Dart =>
      dart ((dart.symm a.symm).1, (dart.symm a.symm).2 + 1)) := by
  sorry
