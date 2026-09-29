-- Prove2me | solution 1 for RLHF.gibbs_zeta_independent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:13:29.852155+00:00
-- url     : https://prove2.me/submissions/9e21070e-6a03-4223-a799-28a32ad87b98

-- Sol generated from NumberTheory/RLHFZetaEulerPolicy.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_gibbs_zeta_policy
import Theorems.Thm_RLHF_localZeta_pos
import Theorems.Thm_RLHF_zetaWeight_mul
import Theorems.Thm_RLHF_zeta_partition_factorizes

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
theorem solution{β s : ℝ} {p q : ℕ} (hβ : 0 < β) (hp : 0 < p) (hq : 0 < q)
    (ab : Smooth A B) :
    gibbsPolicy β (zetaReward β s p q) (uniformDist (Smooth A B)) ab
      = (zetaWeight s (p ^ (ab.1 : ℕ)) / localZeta s p A)
        * (zetaWeight s (q ^ (ab.2 : ℕ)) / localZeta s q B) := by
  have h1 : (0 : ℝ) < localZeta s p A := localZeta_pos hp
  have h2 : (0 : ℝ) < localZeta s q B := localZeta_pos hq
  rw [gibbs_zeta_policy hβ hp hq, zeta_partition_factorizes (A := A) (B := B) hp hq]
  unfold smoothVal
  rw [zetaWeight_mul (pow_pos hp _) (pow_pos hq _)]
  field_simp
