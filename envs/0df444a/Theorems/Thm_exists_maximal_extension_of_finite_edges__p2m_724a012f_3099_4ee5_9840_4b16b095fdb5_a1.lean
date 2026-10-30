-- Prove2me | Theorems.Thm_exists_maximal_extension_of_finite_edges__p2m_724a012f_3099_4ee5_9840_4b16b095fdb5_a1
-- name    : exists_maximal_extension_of_finite_edges__p2m_724a012f_3099_4ee5_9840_4b16b095fdb5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:25:35.112498+00:00
-- url     : https://prove2.me/theorems/803f7e9d-4087-46d8-adf0-598f52d93725
-- title:
--   A finite graph predicate has maximal extensions
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate has an extension that is maximal among predicate-satisfying extensions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_extension_of_finite_edges__p2m_724a012f_3099_4ee5_9840_4b16b095fdb5_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop) (M : SimpleGraph V) (hM : P M) :
    ∃ T : SimpleGraph V, M ≤ T ∧ P T ∧
      (∀ U : SimpleGraph V, T ≤ U → P U → U ≤ T) := by sorry
