-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity_bounded
-- name    : mme_CW_q6_primary_hash_sqrt_capacity_bounded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:49:33.594356+00:00
-- url     : https://prove2.me/theorems/b8f2a34d-d5c0-4cb0-8d0b-b6fd885580dd
-- title:
--   Primary q=6 hash capacity with an explicit uniform fiber cap
-- statement:
--   For every $\tau$ with $3\tau\geq2$, there is a nonnegative constant $C$ such that, for all sufficiently large $N$, the q=6 primary-hash construction produces $A$ outer fibers of common positive size $H$, with $H\leq4^N$, and satisfies the standard cubic-square capacity estimate
--
--   $$R^{2N}e^{-C\sqrt{N+1}}\leq A^3H^2\,S^{3\tau},$$
--
--   where $R=4\cdot6^{3\tau}(6^{3\tau}+2)$ and $S=36^{2G}6^{2L}$ at the usual optimized profile $L=\lfloor\lambda N\rfloor$, $G=N-L$.  This strengthens the existing capacity theorem only by exposing the fiber cap already present in its construction.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5; the primary hash capacity argument with the uniform fiber bound retained.

import Mathlib
import Theorems.Thm_mme_CW_q6_primary_profile_capacity_sqrt_loss
import Theorems.Thm_mme_CW_q6_coupled_exact_floor_pruning
import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss

open MME BigOperators Filter Topology

set_option autoImplicit false

theorem mme_CW_q6_primary_hash_sqrt_capacity_bounded
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
        let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
        let G : ℕ := N - L
        let side : ℕ := 36 ^ (2 * G) * 6 ^ (2 * L)
        let raw : ℝ :=
          4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
        ∃ A H : ℕ,
          ∃ _family : CWQ6PrimaryHashFamily N L G A H,
            H ≤ 4 ^ N ∧
            raw ^ (2 * N) *
                Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
              (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
                ((((side * side * side : ℕ) : ℝ)) ^ tau) := by
  sorry
