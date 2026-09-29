-- Prove2me | solution 1 for PMFrame.card_frameGaps
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:59:56.956196+00:00
-- url     : https://prove2.me/submissions/bbd55141-0ec7-4a76-9037-8fb065d51c48

-- Sol generated from Shared/PMFrameTwoParameter.lean
import Mathlib
import Definitions.Def_Shared_PMFrameTwoParameter
import Theorems.Thm_PMFrame_frameRep_reflect_of_not
import Theorems.Thm_PMFrame_not_frameRep_and_reflect
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



/-! ## 3. Coefficients of the frame geometry count lattice points -/



/-! ## 4. The closed formula -/





/-! ## 5. From the closed formula to the coefficients -/



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
theorem solution{p q : ℕ} (hcop : Nat.Coprime p q) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (frameGaps p q).card * 2 = (p - 1) * (q - 1) := by
  set F := p * q - p - q with hF
  set D := (p - 1) * (q - 1) with hD
  have hpq : p + q ≤ p * q := by nlinarith
  have hDF : D = F + 1 := deg_eq_frobenius_succ hp hq
  have hlt : ∀ n < D, n < p * q := by intro n hn; omega
  have hsym : ∀ n ≤ F, (repPairs p q n = ∅ ↔ ¬ (repPairs p q (F - n) = ∅)) := by
    intro n hn
    rw [repPairs_eq_empty_iff (by omega), repPairs_eq_empty_iff (by omega),
      not_not]
    constructor
    · intro hnot
      exact frameRep_reflect_of_not hcop hp hq n hnot
    · intro hR hR'
      exact not_frameRep_and_reflect hcop hp hq hn hR' hR
  have hcard : (frameGaps p q).card
      = ((range D).filter (fun n => ¬ (repPairs p q n = ∅))).card := by
    refine Finset.card_bij' (fun n _ => F - n) (fun n _ => F - n) ?_ ?_ ?_ ?_
    · intro a ha
      simp only [frameGaps, Finset.mem_filter, Finset.mem_range] at ha ⊢
      exact ⟨by omega, (hsym a (by omega)).1 ha.2⟩
    · intro a ha
      simp only [frameGaps, Finset.mem_filter, Finset.mem_range] at ha ⊢
      refine ⟨by omega, ?_⟩
      exact (hsym (F - a) (by omega)).2
        (by simpa [show F - (F - a) = a by omega] using ha.2)
    · intro a ha
      simp only [frameGaps, Finset.mem_filter, Finset.mem_range] at ha
      show F - (F - a) = a
      omega
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_range] at ha
      show F - (F - a) = a
      omega
  have hsplit : ((range D).filter (fun n => repPairs p q n = ∅)).card
      + ((range D).filter (fun n => ¬ (repPairs p q n = ∅))).card = D := by
    have h := Finset.card_filter_add_card_filter_not (s := range D)
      (fun n => repPairs p q n = ∅)
    simpa using h
  have : (frameGaps p q).card = ((range D).filter (fun n => repPairs p q n = ∅)).card := rfl
  omega
