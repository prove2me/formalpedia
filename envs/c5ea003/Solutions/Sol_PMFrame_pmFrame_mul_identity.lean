-- Prove2me | solution 1 for PMFrame.pmFrame_mul_identity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:01:31.761839+00:00
-- url     : https://prove2.me/submissions/953d7f72-0595-4951-b01a-9ab8e23dfcb7

-- Sol generated from Shared/PMFrameTwoParameter.lean
import Mathlib
import Definitions.Def_Shared_PMFrameTwoParameter
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



/-! ## 3. Coefficients of the frame geometry count lattice points -/



/-! ## 4. The closed formula -/





/-! ## 5. From the closed formula to the coefficients -/



/-! ## 6. Main theorems -/











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
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) :
    ((X : Polynomial ℤ) ^ p - 1) * (X ^ q - 1) * pmFrame (p * q)
      = (X - 1) * (X ^ (p * q) - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hltp : p < p * q := by nlinarith
  have hltq : q < p * q := by nlinarith
  have hdiv : (p * q).divisors = {1, p, q, p * q} := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, -⟩
      obtain ⟨a, b, ha, hb, rfl⟩ := dvd_mul.mp hd
      rcases hp.eq_one_or_self_of_dvd a ha with rfl | rfl <;>
        rcases hq.eq_one_or_self_of_dvd b hb with rfl | rfl <;> simp
    · rintro (rfl | rfl | rfl | rfl) <;> exact ⟨by simp, by omega⟩
  have hprod := Polynomial.prod_cyclotomic_eq_X_pow_sub_one (n := p * q) (by omega) ℤ
  rw [hdiv, Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
    Finset.prod_insert (by simp; omega), Finset.prod_singleton, Polynomial.cyclotomic_one] at hprod
  have hcp : cyclotomic p ℤ * (X - 1) = X ^ p - 1 := Polynomial.cyclotomic_prime_mul_X_sub_one ℤ p
  have hcq : cyclotomic q ℤ * (X - 1) = X ^ q - 1 := Polynomial.cyclotomic_prime_mul_X_sub_one ℤ q
  unfold pmFrame
  calc ((X : Polynomial ℤ) ^ p - 1) * (X ^ q - 1) * cyclotomic (p * q) ℤ
      = (X - 1) * ((X - 1) * (cyclotomic p ℤ * (cyclotomic q ℤ * cyclotomic (p * q) ℤ))) := by
        rw [← hcp, ← hcq]; ring
    _ = (X - 1) * (X ^ (p * q) - 1) := by rw [hprod]
