-- Prove2me | solution 1 for RLHF.gibbs_zeta_policy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:08:40.284814+00:00
-- url     : https://prove2.me/submissions/29f807f8-a0b5-4bc3-ae02-a99b1bcfbab5

-- Sol generated from NumberTheory/RLHFZetaEulerPolicy.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_zetaWeight_pos

/-!
# Euler products from RLHF: the zeta policy on smooth-number response spaces

We instantiate the Gibbs variational principle of `NumberTheory.RLHFGibbsVariational`
with an arithmetic reward model.  The response space is the set of `{p, q}`-smooth
integers `p^a q^b` with bounded exponents, the SFT reference is uniform, and the reward is
the logarithmic (Dirichlet) reward `r(n) = -β s log n`.

The optimal (Gibbs) policy is then the **truncated zeta distribution** `π(n) ∝ n^{-s}`, and
the number-theoretic Euler product manifests itself as a *statistical independence* of the
prime exponents under the aligned policy, together with an *additive* decomposition of the
RLHF free energy over primes.

Main results:

* `RLHF.zeta_partition_factorizes` — Euler factorization of the normalizing constant.
* `RLHF.gibbs_zeta_policy` — the optimal RLHF policy is exactly `n^{-s} / ∑ n^{-s}`.
* `RLHF.gibbs_zeta_independent` — under the optimal policy the prime exponents are
  independent (the policy is a product of two truncated geometric laws).
* `RLHF.freeEnergy_euler_additive` — the RLHF free energy splits additively over the primes.
* `RLHF.smoothVal_injective` — unique factorization: the response space really is a set of
  distinct integers.
* `RLHF.euler_factor_tsum` — removing the exponent cutoff, the local partition function is
  the classical Euler factor `(1 - p^{-s})⁻¹`.
-/

open RLHF

open Finset

/-! ## 1. Uniform reference policies -/



/-! ## 2. The smooth-number response space -/

variable {A B : ℕ}



theorem smoothVal_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (ab : Smooth A B) :
    0 < smoothVal p q ab := by
  unfold smoothVal; positivity


/-! ## 3. The Dirichlet (log) reward and the truncated zeta weights -/







theorem zetaSum_pos {s : ℝ} {p q : ℕ} (hp : 0 < p) (hq : 0 < q) : 0 < zetaSum s p q A B := by
  apply Finset.sum_pos
  · intro ab _; exact zetaWeight_pos (smoothVal_pos hp hq ab)
  · exact univ_nonempty



/-! ## 4. The optimal RLHF policy is the truncated zeta distribution -/

theorem exp_zetaReward {β s : ℝ} {p q : ℕ} (hβ : 0 < β) (hp : 0 < p) (hq : 0 < q)
    (ab : Smooth A B) :
    Real.exp (zetaReward β s p q ab / β) = zetaWeight s (smoothVal p q ab) := by
  have hn : (0 : ℝ) < (smoothVal p q ab : ℝ) := by
    exact_mod_cast smoothVal_pos hp hq ab
  unfold zetaReward zetaWeight
  rw [Real.rpow_def_of_pos hn]
  congr 1
  field_simp

/-- The partition function of the RLHF problem with uniform reference and Dirichlet reward
is the truncated zeta sum, up to the uniform normalization. -/
theorem partition_zetaReward {β s : ℝ} {p q : ℕ} (hβ : 0 < β) (hp : 0 < p) (hq : 0 < q) :
    partition β (zetaReward (A := A) (B := B) β s p q) (uniformDist (Smooth A B))
      = zetaSum s p q A B / (Fintype.card (Smooth A B) : ℝ) := by
  unfold partition zetaSum uniformDist
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun ab _ => ?_)
  rw [exp_zetaReward hβ hp hq]
  ring



/-! ## 5. Additivity of the free energy over primes -/



/-! ## 6. Closed forms and the classical Euler factor -/







open RLHF in
theorem solution{β s : ℝ} {p q : ℕ} (hβ : 0 < β) (hp : 0 < p) (hq : 0 < q)
    (ab : Smooth A B) :
    gibbsPolicy β (zetaReward β s p q) (uniformDist (Smooth A B)) ab
      = zetaWeight s (smoothVal p q ab) / zetaSum s p q A B := by
  have hcard : (0 : ℝ) < (Fintype.card (Smooth A B) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hZ : (0 : ℝ) < zetaSum s p q A B := zetaSum_pos (A := A) (B := B) hp hq
  unfold gibbsPolicy
  rw [partition_zetaReward hβ hp hq, exp_zetaReward hβ hp hq]
  unfold uniformDist
  field_simp
