-- Prove2me | solution 1 for RLHF.gibbs_exponent_zero_marginal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T11:28:03.051299+00:00
-- url     : https://prove2.me/submissions/374e3e49-c582-4d79-ae93-903693481a0b

-- Sol generated from NumberTheory/RLHFZetaDivisibility.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_gibbs_zeta_independent
import Theorems.Thm_RLHF_localZeta_pos

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
theorem solution{β s : ℝ} {p q : ℕ} (hβ : 0 < β) (hp : 0 < p)
    (hq : 0 < q) :
    ∑ b : Fin (B + 1),
        gibbsPolicy β (zetaReward (A := A) (B := B) β s p q) (uniformDist (Smooth A B))
          (⟨0, Nat.succ_pos A⟩, b)
      = 1 / localZeta s p A := by
  have h1 : (0 : ℝ) < localZeta s p A := localZeta_pos hp
  have h2 : (0 : ℝ) < localZeta s q B := localZeta_pos hq
  have hw0 : zetaWeight s (p ^ (0 : ℕ)) = 1 := by
    simp [zetaWeight]
  have hterm : ∀ b : Fin (B + 1),
      gibbsPolicy β (zetaReward (A := A) (B := B) β s p q) (uniformDist (Smooth A B))
          (⟨0, Nat.succ_pos A⟩, b)
        = (1 / localZeta s p A) * (zetaWeight s (q ^ (b : ℕ)) / localZeta s q B) := by
    intro b
    rw [gibbs_zeta_independent hβ hp hq]
    simp only [hw0]
  rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.mul_sum, ← Finset.sum_div]
  have hsum : ∑ b : Fin (B + 1), zetaWeight s (q ^ (b : ℕ)) = localZeta s q B := rfl
  rw [hsum, div_self (ne_of_gt h2), mul_one]
