-- Prove2me | solution 1 for PMFrame.repPair_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:59:57.439993+00:00
-- url     : https://prove2.me/submissions/7d710285-caff-421b-9624-debe4d005173

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
theorem solution{p q : ℕ} (hcop : Nat.Coprime p q) (hq : 0 < q)
    {i j i' j' : ℕ} (hi : i < q) (hi' : i' < q)
    (hE : i * p + j * q = i' * p + j' * q) : i = i' ∧ j = j' := by
  have key : ∀ a b c d : ℕ, b < q → a ≤ b → a * p + c * q = b * p + d * q → a = b := by
    intro a b c d hb hab hE
    have hcd : d ≤ c := by nlinarith [Nat.sub_add_cancel hab]
    have h1 : (b - a) * p = (c - d) * q := by
      have e1 : (b - a) * p + a * p = b * p := by rw [← Nat.add_mul, Nat.sub_add_cancel hab]
      have e2 : (c - d) * q + d * q = c * q := by rw [← Nat.add_mul, Nat.sub_add_cancel hcd]
      omega
    have hdvd : q ∣ (b - a) * p := ⟨c - d, by rw [h1]; ring⟩
    have hqa : q ∣ (b - a) := Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm hcop) hdvd
    rcases Nat.eq_zero_or_pos (b - a) with h0 | h0
    · omega
    · have := Nat.le_of_dvd h0 hqa; omega
  have hij : i = i' := by
    rcases le_total i i' with h | h
    · exact key i i' j j' hi' h hE
    · exact (key i' i j' j hi h hE.symm).symm
  subst hij
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_right hq (by omega)⟩
