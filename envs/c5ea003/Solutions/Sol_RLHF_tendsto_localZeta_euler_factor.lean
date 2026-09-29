-- Prove2me | solution 1 for RLHF.tendsto_localZeta_euler_factor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:25:07.799194+00:00
-- url     : https://prove2.me/submissions/07986334-2468-47ff-82a0-b20698486cd6

-- Sol generated from NumberTheory/RLHFZetaDivisibility.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_localZeta_geom
import Theorems.Thm_RLHF_zetaWeight_lt_one
import Theorems.Thm_RLHF_zetaWeight_pos

/-!
# Divisibility statistics of the aligned (zeta) policy

For the Dirichlet reward on the `{p,q}`-smooth response space, the optimal RLHF policy is
the truncated zeta distribution (`RLHF.gibbs_zeta_policy`).  Here we compute the
*arithmetic* statistics of the responses it emits.

* `RLHF.gibbs_exponent_zero_marginal` — the probability that the sampled response is
  **not divisible** by `p` equals `1 / localZeta s p A`.
* `RLHF.prob_dvd_lt_zetaWeight` — hence the probability that `p` divides the sampled
  response is strictly below `p^{-s}`, the classical Dirichlet density.
* `RLHF.tendsto_localZeta_euler_factor`, `RLHF.tendsto_prob_not_dvd` — as the exponent
  cutoff is lifted, these statistics converge exactly to the Golomb–Dirichlet values
  `1 - p^{-s}`: alignment reproduces the density of `p`-indivisible integers.
-/

open RLHF

open Finset Filter Topology

variable {A B : ℕ}






open RLHF in
theorem solution{s : ℝ} {p : ℕ} (hp : 2 ≤ p) (hs : 0 < s) :
    Tendsto (fun A : ℕ => localZeta s p A) atTop (𝓝 (1 - zetaWeight s p)⁻¹) := by
  have hp0 : 0 < p := by omega
  have hlt : zetaWeight s p < 1 := zetaWeight_lt_one hp hs
  have hnn : 0 ≤ zetaWeight s p := (zetaWeight_pos hp0).le
  have hne : zetaWeight s p ≠ 1 := ne_of_lt hlt
  have hpow : Tendsto (fun A : ℕ => zetaWeight s p ^ (A + 1)) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hnn hlt
    exact h.comp (tendsto_add_atTop_nat 1)
  have hform : ∀ A : ℕ, localZeta s p A
      = (zetaWeight s p ^ (A + 1) - 1) / (zetaWeight s p - 1) :=
    fun A => localZeta_geom hp0 hne
  have hlim : Tendsto (fun A : ℕ => (zetaWeight s p ^ (A + 1) - 1) / (zetaWeight s p - 1))
      atTop (𝓝 ((0 - 1) / (zetaWeight s p - 1))) :=
    ((hpow.sub tendsto_const_nhds).div_const _)
  have heq : (0 - 1) / (zetaWeight s p - 1) = (1 - zetaWeight s p)⁻¹ := by
    rw [eq_comm, inv_eq_iff_eq_inv]
    field_simp
    ring
  rw [heq] at hlim
  simpa [hform] using hlim
