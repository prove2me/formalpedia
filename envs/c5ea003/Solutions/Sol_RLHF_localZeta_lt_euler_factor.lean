-- Prove2me | solution 1 for RLHF.localZeta_lt_euler_factor
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:03:09.11256+00:00
-- url     : https://prove2.me/submissions/50216969-b3a8-4d6a-9f3b-ed6cfab467bc

-- Sol generated from NumberTheory/RLHFZetaEulerPolicy.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFGibbsVariational
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_localZeta_geom
import Theorems.Thm_RLHF_zetaWeight_lt_one
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





/-! ## 3. The Dirichlet (log) reward and the truncated zeta weights -/










/-! ## 4. The optimal RLHF policy is the truncated zeta distribution -/





/-! ## 5. Additivity of the free energy over primes -/



/-! ## 6. Closed forms and the classical Euler factor -/







open RLHF in
theorem solution{s : ℝ} {p A : ℕ} (hp : 2 ≤ p) (hs : 0 < s) :
    localZeta s p A < (1 - zetaWeight s p)⁻¹ := by
  have hp0 : 0 < p := by omega
  have hlt : zetaWeight s p < 1 := zetaWeight_lt_one hp hs
  have hnn : 0 ≤ zetaWeight s p := (zetaWeight_pos hp0).le
  have hx : 0 < zetaWeight s p ^ (A + 1) := pow_pos (zetaWeight_pos hp0) _
  have hne : zetaWeight s p ≠ 1 := ne_of_lt hlt
  rw [localZeta_geom hp0 hne]
  rw [div_lt_iff_of_neg (by linarith : zetaWeight s p - 1 < 0)]
  have h0 : (1 : ℝ) - zetaWeight s p ≠ 0 := by linarith
  have hinv : (1 - zetaWeight s p)⁻¹ * (zetaWeight s p - 1) = -1 := by
    rw [inv_mul_eq_div, div_eq_iff h0]; ring
  rw [hinv]
  linarith
