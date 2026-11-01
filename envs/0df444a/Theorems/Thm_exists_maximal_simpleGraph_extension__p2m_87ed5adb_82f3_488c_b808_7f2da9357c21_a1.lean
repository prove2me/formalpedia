-- Prove2me | Theorems.Thm_exists_maximal_simpleGraph_extension__p2m_87ed5adb_82f3_488c_b808_7f2da9357c21_a1
-- name    : exists_maximal_simpleGraph_extension__p2m_87ed5adb_82f3_488c_b808_7f2da9357c21_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:47:15.262199+00:00
-- url     : https://prove2.me/theorems/02cffa31-44ea-42b2-a9e1-e4429b8a8c34
-- title:
--   Finite maximal extension among simple graphs
-- statement:
--   For a finite vertex type, any property of simple graphs that holds of a given graph has a supergraph satisfying the property that is maximal under edge inclusion among graphs with that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_simpleGraph_extension__p2m_87ed5adb_82f3_488c_b808_7f2da9357c21_a1
    {V : Type} [Fintype V]
    (L : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P L) :
    ∃ H : SimpleGraph V, L ≤ H ∧ P H ∧
      ∀ K : SimpleGraph V, H ≤ K → P K → K = H := by sorry
