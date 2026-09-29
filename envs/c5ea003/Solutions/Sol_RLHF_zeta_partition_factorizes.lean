-- Prove2me | solution 1 for RLHF.zeta_partition_factorizes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:11:40.491504+00:00
-- url     : https://prove2.me/submissions/da7929ea-abf4-4c75-a215-93040e6e23c7

-- Sol generated from NumberTheory/RLHFZetaEulerPolicy.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_zetaWeight_mul

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





/-! ## 3. The Dirichlet (log) reward and the truncated zeta weights -/










/-! ## 4. The optimal RLHF policy is the truncated zeta distribution -/





/-! ## 5. Additivity of the free energy over primes -/



/-! ## 6. Closed forms and the classical Euler factor -/







open RLHF in
theorem solution{s : ℝ} {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    zetaSum s p q A B = localZeta s p A * localZeta s q B := by
  unfold zetaSum localZeta
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  exact zetaWeight_mul (pow_pos hp _) (pow_pos hq _)
