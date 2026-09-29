-- Prove2me | solution 1 for RLHF.freeEnergy_multi_lt_euler
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:08:38.727784+00:00
-- url     : https://prove2.me/submissions/2c5f9e6b-77a6-4004-8803-482be52d7deb

-- Sol generated from NumberTheory/RLHFEulerProductGeneral.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFEulerProductGeneral
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_localZeta_lt_euler_factor
import Theorems.Thm_RLHF_localZeta_pos
import Theorems.Thm_RLHF_zetaWeight_lt_one

/-!
# The full Euler product of an aligned policy: arbitrarily many primes

`NumberTheory.RLHFZetaEulerPolicy` treated the two-prime smooth response space.  Here we
carry the construction to a response space built from `k` primes with individually bounded
exponents,

`Ω = Π i, Fin (A i + 1)`,   `n(a) = ∏ i, (P i) ^ (a i)`,

and the Dirichlet reward `r(n) = -β s log n`.  The results:

* `RLHF.zetaWeight_prod` — complete multiplicativity of `n ↦ n^{-s}` over finite products.
* `RLHF.zetaSumMulti_eq_prod` — the **Euler product**: the partition function of the
  aligned policy factors as `∏ i, localZeta s (P i) (A i)`.
* `RLHF.gibbs_multi_independent` — the aligned policy is the product of its per-prime
  marginals: *all* prime exponents are mutually independent under RLHF alignment.
* `RLHF.freeEnergy_multi_additive` — the RLHF free energy is a sum of per-prime terms.
* `RLHF.freeEnergy_multi_lt_euler` — a Mertens-type strict upper bound by the genuine
  Euler factors `-∑ log (1 - P i ^ {-s})`.
-/

open RLHF

open Finset

variable {k : ℕ}

/-! ## 1. Multi-prime smooth response spaces -/





/-! ## 2. The Euler product for the partition function -/




/-! ## 3. The aligned policy and its independence structure -/






/-! ## 4. Additivity of the free energy over the primes -/




open RLHF in
theorem solution{s : ℝ} {P : Fin k → ℕ} {A : Fin k → ℕ}
    (hk : 0 < k) (hP : ∀ i, 2 ≤ P i) (hs : 0 < s) :
    (∑ i, Real.log (localZeta s (P i) (A i)))
      < -∑ i, Real.log (1 - zetaWeight s (P i)) := by
  have hne : (univ : Finset (Fin k)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp hk
  have hterm : ∀ i ∈ (univ : Finset (Fin k)),
      Real.log (localZeta s (P i) (A i)) < -Real.log (1 - zetaWeight s (P i)) := by
    intro i _
    have hp0 : 0 < P i := by have := hP i; omega
    have hlt1 : zetaWeight s (P i) < 1 := zetaWeight_lt_one (hP i) hs
    have hpos : 0 < 1 - zetaWeight s (P i) := by linarith
    have hL : 0 < localZeta s (P i) (A i) := localZeta_pos hp0
    have hbound : localZeta s (P i) (A i) < (1 - zetaWeight s (P i))⁻¹ :=
      localZeta_lt_euler_factor (hP i) hs
    have := Real.log_lt_log hL hbound
    rwa [Real.log_inv] at this
  have := Finset.sum_lt_sum_of_nonempty hne hterm
  simpa [Finset.sum_neg_distrib] using this
