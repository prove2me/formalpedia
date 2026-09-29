-- Prove2me | solution 1 for PMFrame.coeff_frameGeom_eq_indicator
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:01:30.317698+00:00
-- url     : https://prove2.me/submissions/bf4ef7ce-171a-47b1-a467-7c80f2c9e804

-- Sol generated from Shared/PMFrameTwoParameter.lean
import Mathlib
import Definitions.Def_Shared_PMFrameTwoParameter
import Theorems.Thm_PMFrame_repPair_unique
import Theorems.Thm_PMFrame_repPairs_nonempty_iff
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


/-! ## 4. The closed formula -/





/-! ## 5. From the closed formula to the coefficients -/



/-! ## 6. Main theorems -/











/-! ## 7. Balance: the signs sum to one -/


/-! ## 8. Sharpness of the bound `-1` -/


/-! ## 9. The numerical semigroup `⟨p,q⟩` and the exact sign pattern -/



theorem repPairs_eq_empty_iff {p q n : ℕ} (hn : n < p * q) :
    repPairs p q n = ∅ ↔ ¬ FrameRep p q n := by
  rw [← Finset.not_nonempty_iff_eq_empty, repPairs_nonempty_iff hn]



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
    {n : ℕ} (hn : n < p * q) [Decidable (FrameRep p q n)] :
    (frameGeom p q).coeff n = if FrameRep p q n then 1 else 0 := by
  rw [coeff_frameGeom]
  by_cases hR : FrameRep p q n
  · rw [if_pos hR]
    have hne : (repPairs p q n).Nonempty := (repPairs_nonempty_iff hn).2 hR
    have h1 : 1 ≤ (repPairs p q n).card := Finset.card_pos.2 hne
    have h2 := card_repPairs_le_one hcop hq n
    have : (repPairs p q n).card = 1 := by omega
    simp [this]
  · rw [if_neg hR]
    have : repPairs p q n = ∅ := (repPairs_eq_empty_iff hn).2 hR
    simp [this]
