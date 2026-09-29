-- Prove2me | solution 1 for RLHF.localZeta_geom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:58:43.67649+00:00
-- url     : https://prove2.me/submissions/247d4581-3c48-4adc-833a-26578f2901f3

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

theorem zetaWeight_pow {s : ℝ} {p : ℕ} (hp : 0 < p) (a : ℕ) :
    zetaWeight s (p ^ a) = (zetaWeight s p) ^ a := by
  have hx : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  unfold zetaWeight
  rw [Nat.cast_pow, ← Real.rpow_natCast (p : ℝ) a, ← Real.rpow_natCast ((p : ℝ) ^ (-s)) a,
    ← Real.rpow_mul hx.le, ← Real.rpow_mul hx.le]
  ring_nf






open RLHF in
theorem solution{s : ℝ} {p A : ℕ} (hp : 0 < p) (hne : zetaWeight s p ≠ 1) :
    localZeta s p A = ((zetaWeight s p) ^ (A + 1) - 1) / (zetaWeight s p - 1) := by
  unfold localZeta
  rw [show (∑ a : Fin (A + 1), zetaWeight s (p ^ (a : ℕ)))
      = ∑ a ∈ Finset.range (A + 1), zetaWeight s (p ^ a) by
    rw [Finset.sum_range fun a => zetaWeight s (p ^ a)]]
  rw [Finset.sum_congr rfl (fun a _ => zetaWeight_pow hp a)]
  exact geom_sum_eq hne (A + 1)
