-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_disconnected_partition__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a2
-- name    : WilliamsonShmoys.exists_disconnected_partition__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:10:21.039916+00:00
-- url     : https://prove2.me/theorems/47aa33f0-d05a-4e2e-8902-ab2363ad3928
-- title:
--   A disconnected finite graph has a nontrivial partition with no cross edges
-- statement:
--   A disconnected finite graph has a nonempty proper vertex subset with no edges crossing between it and its complement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_disconnected_partition__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a2
    {V : Type} [Fintype V] (M : SimpleGraph V) (hdisc : ¬ M.Connected) :
    ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      (∀ ⦃u v : V⦄, u ∈ A → v ∈ Aᶜ → ¬ M.Adj u v) := by
  sorry
