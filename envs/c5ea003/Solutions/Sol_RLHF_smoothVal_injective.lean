-- Prove2me | solution 1 for RLHF.smoothVal_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:17:42.943378+00:00
-- url     : https://prove2.me/submissions/1cc787d6-7695-48b3-bb79-0aae3a855bae

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
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Function.Injective (smoothVal (A := A) (B := B) p q) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [smoothVal] at h
  have hpne : p ^ (a : ℕ) ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hqne : q ^ (b : ℕ) ≠ 0 := pow_ne_zero _ hq.pos.ne'
  have hpne' : p ^ (c : ℕ) ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have hqne' : q ^ (d : ℕ) ≠ 0 := pow_ne_zero _ hq.pos.ne'
  have hfp := congrArg (fun n : ℕ => n.factorization p) h
  have hfq := congrArg (fun n : ℕ => n.factorization q) h
  simp only [Nat.factorization_mul hpne hqne, Nat.factorization_mul hpne' hqne',
    hp.factorization_pow, hq.factorization_pow, Finsupp.coe_add, Pi.add_apply,
    Finsupp.single_apply, if_neg hpq, if_neg (Ne.symm hpq)] at hfp hfq
  have ha : (a : ℕ) = (c : ℕ) := by simpa using hfp
  have hb : (b : ℕ) = (d : ℕ) := by simpa using hfq
  exact Prod.ext (Fin.ext ha) (Fin.ext hb)
