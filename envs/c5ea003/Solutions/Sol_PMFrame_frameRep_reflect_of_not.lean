-- Prove2me | solution 1 for PMFrame.frameRep_reflect_of_not
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:57:57.628334+00:00
-- url     : https://prove2.me/submissions/416d7b66-1a8b-4bc3-8c3c-3e84271c402b

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
theorem solution{p q : ℕ} (hcop : Nat.Coprime p q) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (n : ℕ) (h1 : ¬ FrameRep p q n) : FrameRep p q (p * q - p - q - n) := by
  haveI : NeZero p := ⟨by omega⟩
  have hpq : p + q ≤ p * q := by nlinarith
  have hunit : IsUnit (q : ZMod p) := (ZMod.isUnit_iff_coprime q p).2 hcop.symm
  set x : ZMod p := (n : ZMod p) * (↑q)⁻¹ with hx
  set j : ℕ := x.val with hj
  have hjlt : j < p := ZMod.val_lt x
  have hmod : (j * q : ℕ) ≡ n [MOD p] := by
    have hz : ((j * q : ℕ) : ZMod p) = ((n : ℕ) : ZMod p) := by
      push_cast
      rw [hj, ZMod.natCast_val, ZMod.cast_id, hx, mul_assoc, ZMod.inv_mul_of_unit _ hunit, mul_one]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 hz
  have hgt : n < j * q := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hcon).1 hmod
    exact h1 ⟨c, j, by rw [mul_comm c p]; omega⟩
  obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hgt.le).1 hmod.symm
  have hcpos : 0 < c := by
    rcases Nat.eq_zero_or_pos c with rfl | hcp
    · simp at hc; omega
    · exact hcp
  obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, p = j + e + 1 := ⟨p - 1 - j, by omega⟩
  refine ⟨d, e, ?_⟩
  have hring : (j + e + 1) * q = j * q + e * q + q := by ring
  have hsum : j * q + e * q + q = p * q := by rw [← hring, ← he]
  have hexp : p * (d + 1) = d * p + p := by ring
  omega
