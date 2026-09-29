-- Prove2me | solution 1 for PMFrame.coeff_pmFrame_two_param_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:04:44.227907+00:00
-- url     : https://prove2.me/submissions/1f8a2081-754d-40ca-ac02-2abdc07dcdfe

-- Sol generated from Shared/PMFrameTwoParameter.lean
import Mathlib
import Definitions.Def_Shared_PMFrameTwoParameter
import Theorems.Thm_PMFrame_pmFrame_closed_formula
import Theorems.Thm_PMFrame_repPair_unique
/-
# The two-parameter ±-frame: coefficients of binary cyclotomic polynomials

## Research thread

The *±-frame* of order `n` is the `n`-th cyclotomic polynomial `Φₙ ∈ ℤ[X]`, viewed
as a signed frame: the interesting question is how negative a coefficient can be.

* **One-parameter case (already a theorem).**  For a prime `p`,
  `Φ_p = 1 + X + ⋯ + X^{p-1}`, so every coefficient is `0` or `1`; in particular
  every coefficient — the head coefficient included — is `≥ -1`.  This is
  `headCoeff_pmFrame_ge_neg_one` below.

* **Two-parameter case (this file).**  For two *distinct* primes `p ≠ q` the
  closed formula

      Φ_{pq}(X) · (X^{pq} - 1) = (X - 1) · G_{p,q}(X),
      G_{p,q}(X) = (∑_{i<q} X^{ip}) · (∑_{j<p} X^{jq})

  turns the question into a statement about **integer points in a
  two-dimensional region**: the coefficient of `X^n` in `G_{p,q}` counts the
  lattice points `(i,j)` of the box `[0,q) × [0,p)` on the line `ip + jq = n`,
  and the *balance / cycle-type* constraint `i < q`, `j < p` forces that count to
  be `0` or `1`.  Consequently

      Φ_{pq}.coeff n = G.coeff n - G.coeff (n-1) ∈ {-1, 0, 1}

  for every `n`, which is Migotti's theorem.  The arithmetic core is a pure
  `omega`/`nlinarith` statement about the box (`repPair_unique`).

* **Sharpness.**  The bound `-1` is attained: `Φ₁₅.coeff 7 = -1`
  (`coeff_pmFrame_fifteen_seven`), proved from the closed formula by counting the
  (empty) set of lattice points on `3i + 5j = 7` inside `[0,5) × [0,3)`.

* **Balance.**  `Φ_{pq}(1) = 1`, so along the frame the `+1`'s outnumber the
  `-1`'s by exactly one (`pmFrame_coeff_sum_eq_one`).

Everything is proved from scratch on top of mathlib's `Polynomial.cyclotomic`.
-/

open PMFrame

open Polynomial Finset

/-! ## 1. The ±-frame and its two-parameter geometric companion -/




/-! ## 2. The arithmetic core: uniqueness of lattice points in the balance box -/


/-- The balance box meets each line in at most one lattice point. -/
theorem card_repPairs_le_one {p q : ℕ} (hcop : Nat.Coprime p q) (hq : 0 < q) (n : ℕ) :
    (repPairs p q n).card ≤ 1 := by
  rw [Finset.card_le_one]
  rintro ⟨i, j⟩ ha ⟨i', j'⟩ hb
  simp only [repPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ha hb
  obtain ⟨⟨hi, hj⟩, hE⟩ := ha
  obtain ⟨⟨hi', hj'⟩, hE'⟩ := hb
  obtain ⟨h1, h2⟩ := repPair_unique hcop hq hi hi' (hE.trans hE'.symm)
  simp [h1, h2]

/-! ## 3. Coefficients of the frame geometry count lattice points -/

theorem coeff_frameGeom (p q n : ℕ) :
    (frameGeom p q).coeff n = ((repPairs p q n).card : ℤ) := by
  unfold frameGeom repPairs
  rw [Finset.sum_mul_sum, Polynomial.finset_sum_coeff]
  simp only [Polynomial.finset_sum_coeff, ← pow_add, Polynomial.coeff_X_pow]
  rw [← Finset.sum_product', Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : x.1 * p + x.2 * q = n
  · simp [h]
  · simp only [h, if_false, ite_eq_right_iff]
    omega

/-- Every coefficient of the frame geometry is `0` or `1`. -/
theorem coeff_frameGeom_le_one {p q : ℕ} (hcop : Nat.Coprime p q) (hq : 0 < q) (n : ℕ) :
    0 ≤ (frameGeom p q).coeff n ∧ (frameGeom p q).coeff n ≤ 1 := by
  rw [coeff_frameGeom]
  have := card_repPairs_le_one hcop hq n
  constructor
  · positivity
  · exact_mod_cast this

/-! ## 4. The closed formula -/





/-! ## 5. From the closed formula to the coefficients -/

/-- Below the exponent `pq`, the coefficients of the ±-frame are the successive
differences of the lattice-point counts. -/
theorem coeff_pmFrame_succ {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    {n : ℕ} (hn : n + 1 < p * q) :
    (pmFrame (p * q)).coeff (n + 1)
      = (frameGeom p q).coeff (n + 1) - (frameGeom p q).coeff n := by
  have hform := congrArg (fun f => Polynomial.coeff f (n + 1)) (pmFrame_closed_formula hp hq h)
  simp only [mul_sub, sub_mul, Polynomial.coeff_sub, mul_one, one_mul] at hform
  rw [Polynomial.coeff_mul_X_pow'] at hform
  rw [if_neg (by omega)] at hform
  rw [Polynomial.coeff_X_mul] at hform
  linarith [hform]

theorem coeff_pmFrame_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    (hpq : 0 < p * q) :
    (pmFrame (p * q)).coeff 0 = (frameGeom p q).coeff 0 := by
  have hform := congrArg (fun f => Polynomial.coeff f 0) (pmFrame_closed_formula hp hq h)
  simp only [mul_sub, sub_mul, Polynomial.coeff_sub, mul_one, one_mul] at hform
  rw [Polynomial.coeff_mul_X_pow'] at hform
  rw [if_neg (by omega)] at hform
  simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul] at hform
  linarith [hform]

/-! ## 6. Main theorems -/

private lemma deg_eq_frobenius_succ {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (p - 1) * (q - 1) = (p * q - p - q) + 1 := by
  obtain ⟨a, rfl⟩ : ∃ a, p = a + 2 := ⟨p - 2, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, q = b + 2 := ⟨q - 2, by omega⟩
  have h : (a + 2) * (b + 2) = a * b + 2 * a + 2 * b + 4 := by ring
  have h2 : (a + 2 - 1) * (b + 2 - 1) = a * b + a + b + 1 := by
    have ea : a + 2 - 1 = a + 1 := by omega
    have eb : b + 2 - 1 = b + 1 := by omega
    rw [ea, eb]; ring
  omega

/-- The degree of a semiprime ±-frame. -/
theorem natDegree_pmFrame {p q : ℕ} (hcop : Nat.Coprime p q) (hp : p.Prime) (hq : q.Prime) :
    (pmFrame (p * q)).natDegree = (p - 1) * (q - 1) := by
  unfold pmFrame
  rw [Polynomial.natDegree_cyclotomic, Nat.totient_mul hcop,
    Nat.totient_prime hp, Nat.totient_prime hq]









/-! ## 7. Balance: the signs sum to one -/


/-! ## 8. Sharpness of the bound `-1` -/


/-! ## 9. The numerical semigroup `⟨p,q⟩` and the exact sign pattern -/






/-! ## 10. Sharpness for **every** semiprime -/






/-! ## 11. Sylvester symmetry of the balance region -/





/-! ## 12. Sylvester's gap count -/



/-! ## 13. Palindromicity from the Sylvester symmetry -/


/-! ## 14. The coprimality boundary

Adversarial check: the whole argument rests on `repPair_unique`, whose only
input is coprimality of the two steps.  Without it the balance box really does
contain two lattice points on one line and the frame geometry acquires a
coefficient `2`, so the `{-1,0,1}` conclusion genuinely fails.  This pins down
coprimality as the exact boundary of the method. -/




open PMFrame in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q)
    (k : ℕ) : |(pmFrame (p * q)).coeff k| ≤ 1 := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 h
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hq0 : 0 < q := hq.pos
  rcases lt_or_ge k (p * q) with hk | hk
  · match k with
    | 0 =>
        rw [coeff_pmFrame_zero hp hq h (by omega)]
        obtain ⟨h0, h1⟩ := coeff_frameGeom_le_one hcop hq0 0
        rw [abs_le]; omega
    | (n + 1) =>
        rw [coeff_pmFrame_succ hp hq h hk]
        obtain ⟨h0, h1⟩ := coeff_frameGeom_le_one hcop hq0 (n + 1)
        obtain ⟨h2, h3⟩ := coeff_frameGeom_le_one hcop hq0 n
        rw [abs_le]; omega
  · have hpq : p + q ≤ p * q := by nlinarith
    have hlt : (pmFrame (p * q)).natDegree < k := by
      rw [natDegree_pmFrame hcop hp hq, deg_eq_frobenius_succ hp2 hq2]
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt]
    norm_num
