-- Prove2me | solution 1 for BatchSmoothness.smooth_iff_dvd_primorial_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:15:03.271377+00:00
-- url     : https://prove2.me/submissions/5cbdc19d-57de-44dc-9523-6bad79a71b59

-- Sol generated from Applications/BatchSmoothnessCorrectness.lean
import Mathlib
import Definitions.Def_Applications_BatchSmoothnessCorrectness

/-!
# Exactness of product-tree batch smoothness testing

Experiment 561 ("BATCH-WINS-TESTING") compared *product-tree batch smoothness
testing* against *solo trial division* on pools of `k ∈ {1, 8, 64, 512}`
candidates with smoothness bound `B = 100` and candidates of bit length `40`.
Alongside the cost measurement (formalised in
`Catalog/Applications/BatchSmoothnessCost.lean`) the experiment ran an
**exact-match audit**: the smooth set reported by the batch algorithm agreed
with per-item trial division on 500/500 samples, in all three variants
(tree-vs-trial, direct-vs-trial, vector).

This file replaces that finite audit by a theorem: the batch criterion and
trial division agree on *every* input in the tested range, not merely on 500
samples.

## The algorithm being modelled

Let `P = ∏ {p prime : p ≤ B}` (`primorialUpTo B`).  Bernstein's batch test
computes, for each candidate `n`, the residue `P mod n` in a remainder tree and
then squares it `e` times modulo `n`; it declares `n` smooth exactly when the
result is `0 mod n`, i.e. exactly when `n ∣ P ^ (2 ^ e)`.

## Main results

* `smooth_iff_dvd_primorial_pow` — the exponent criterion:
  for `0 < n < 2 ^ t`, `n` is `B`-smooth **iff** `n ∣ P ^ t`.
  (Both directions are needed: `←` is soundness, `→` is completeness, and
  completeness is exactly where the bit-length bound `n < 2 ^ t` enters.)
* `smooth_iff_dvd_primorial_pow_two_pow` — the repeated-squaring form actually
  implemented: any `e` with `t ≤ 2 ^ e` works.
* `smooth_iff_mod_criterion` — the criterion survives the modular reduction
  performed by the remainder tree.
* `exponent_sharp` — the bit-length bound is sharp: `2 ^ t ∤ P ^ s` for `s < t`,
  so no smaller exponent can be used.
* `ProdTree.eval_eq_leaves_prod` and `ProdTree.eval_eq_primorial` — the value of
  a product tree is independent of its shape, which is why the "tree" and
  "direct" arms of the audit cannot disagree.
* `batch_filter_eq_trial_filter` — the audit statement itself: on any finite
  pool of candidates below `2 ^ t`, the batch-detected smooth set **equals** the
  trial-division smooth set.
* `batch_audit_500` — a machine-checked instance of the audit on the pool
  `{1, …, 500}` with `B = 100`.
-/

open BatchSmoothness

open Finset

/-! ## The batch modulus -/


lemma primorialUpTo_pos (B : ℕ) : 0 < primorialUpTo B :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primesBelow hp).pos

lemma primorial_ne_zero (B : ℕ) : primorialUpTo B ≠ 0 := ((primorialUpTo_pos B)).ne'

/-- The factor base is squarefree: every prime `≤ B` occurs in `P` exactly once. -/
lemma factorization_primorial {B p : ℕ} (hp : p.Prime) (hpB : p ≤ B) :
    (primorialUpTo B).factorization p = 1 := by
  unfold primorialUpTo
  rw [Nat.factorization_prod (fun q hq => (Nat.prime_of_mem_primesBelow hq).ne_zero)]
  simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single p]
  · simp [Nat.Prime.factorization hp]
  · intro q hq hqp
    rw [Nat.Prime.factorization (Nat.prime_of_mem_primesBelow hq)]
    simp [Ne.symm hqp]
  · intro h
    exact absurd (Nat.mem_primesBelow.mpr ⟨by omega, hp⟩) h

/-- A prime divides the batch modulus exactly when it lies in the factor base. -/
lemma prime_dvd_primorial_iff {B p : ℕ} (hp : p.Prime) :
    p ∣ primorialUpTo B ↔ p ≤ B := by
  constructor
  · intro h
    obtain ⟨q, hq, hpq⟩ := (Nat.Prime.prime hp).exists_mem_finset_dvd h
    have hq' := Nat.prime_of_mem_primesBelow hq
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp hq').mp hpq
    have := Nat.lt_of_mem_primesBelow hq
    omega
  · intro h
    exact Nat.dvd_of_factorization_pos (by rw [factorization_primorial hp h]; omega)

/-! ## Smoothness -/



/-! ## The batch criterion is exactly smoothness -/






/-! ## Tree shape is irrelevant (the "tree vs direct" arm of the audit) -/


open ProdTree






/-! ## The audit, as a theorem -/




open BatchSmoothness in
theorem solution{B n t : ℕ} (hn : 0 < n) (hnt : n < 2 ^ t) :
    IsSmooth B n ↔ n ∣ (primorialUpTo B) ^ t := by
  constructor
  · intro hs
    rw [← Nat.factorization_le_iff_dvd hn.ne' (pow_ne_zero _ (primorial_ne_zero B))]
    intro p
    by_cases hp : p.Prime
    · by_cases hpn : p ∣ n
      · have hpB := hs p hp hpn
        rw [Nat.factorization_pow]
        simp only [Finsupp.smul_apply, smul_eq_mul, factorization_primorial hp hpB, mul_one]
        have hdvd : p ^ (n.factorization p) ∣ n := Nat.ordProj_dvd n p
        have h2 : 2 ^ (n.factorization p) ≤ p ^ (n.factorization p) :=
          Nat.pow_le_pow_left hp.two_le _
        have h3 : p ^ (n.factorization p) ≤ n := Nat.le_of_dvd hn hdvd
        have h4 : (2 : ℕ) ^ (n.factorization p) < 2 ^ t := lt_of_le_of_lt (le_trans h2 h3) hnt
        have := (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp h4
        omega
      · simp [Nat.factorization_eq_zero_of_not_dvd hpn]
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · intro hd p hp hpn
    exact (prime_dvd_primorial_iff hp).mp (hp.dvd_of_dvd_pow (hpn.trans hd))
