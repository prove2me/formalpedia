-- Prove2me | solution 1 for RLHF.zetaWeight_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:08:40.873343+00:00
-- url     : https://prove2.me/submissions/d0a884fd-11bc-4918-ad45-685afd3ebd6f

-- Sol generated from NumberTheory/RLHFZetaEulerPolicy.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy

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
theorem solution{s : ℝ} {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    zetaWeight s (m * n) = zetaWeight s m * zetaWeight s n := by
  have hm' : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have hn' : (0 : ℝ) ≤ (n : ℝ) := by positivity
  unfold zetaWeight
  rw [Nat.cast_mul, Real.mul_rpow hm' hn']
