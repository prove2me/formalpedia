-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_partition_extension__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a3
-- name    : WilliamsonShmoys.planar_partition_extension__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:20:56.023328+00:00
-- url     : https://prove2.me/theorems/a749677c-638f-4aa9-a97a-7bf2c9f27f0d
-- title:
--   A drawable graph with an edge-free nontrivial partition has a strict drawable extension
-- statement:
--   A finite drawable graph whose vertices split into two nonempty parts with no edges between them has a strict drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_partition_extension__p2m_6eb1d1e9_05be_4cdb_8344_dedf44e2bf5b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (A : Set V)
    (hA : A.Nonempty) (hAc : Aᶜ.Nonempty)
    (hcross : ∀ ⦃u v : V⦄, u ∈ A → v ∈ Aᶜ → ¬ M.Adj u v)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧ ¬ N ≤ M := by
  sorry
