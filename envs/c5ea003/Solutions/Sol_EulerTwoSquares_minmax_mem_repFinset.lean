-- Prove2me | solution 1 for EulerTwoSquares.minmax_mem_repFinset
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T12:52:03.477692+00:00
-- url     : https://prove2.me/submissions/16d6fe38-815d-47e1-ac41-98d77b101552

-- Sol generated from Algebra/EulerTwoSquaresRepCount.lean
import Mathlib
import Definitions.Def_Algebra_EulerTwoSquaresRepCount

/-!
# The representation count, as a finite cardinality

`EulerTwoSquares.exactly_two_reps` describes the representations of `p*q` as a list of four
ordered integer pairs.  Here we package the same information as a *cardinality*: the finite
set of normalised representations

`repFinset n = {(a,b) : 0 < a ≤ b, a² + b² = n}`

has exactly two elements when `n = p*q` for distinct primes `p ≡ q ≡ 1 [MOD 4]`.  This is the
form in which the eligibility statistics of a factorisation experiment are actually measured.
-/

open EulerTwoSquares

variable {p q : ℕ}


theorem mem_repFinset {n : ℕ} {z : ℕ × ℕ} :
    z ∈ repFinset n ↔ 0 < z.1 ∧ z.1 ≤ z.2 ∧ z.1 ^ 2 + z.2 ^ 2 = n := by
  simp only [repFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2, h3⟩
    have hz1 : z.1 ≤ z.1 ^ 2 := Nat.le_self_pow (by norm_num) _
    have hz2 : z.2 ≤ z.2 ^ 2 := Nat.le_self_pow (by norm_num) _
    exact ⟨⟨by omega, by omega⟩, h1, h2, h3⟩






open EulerTwoSquares in
theorem solution{n : ℕ} {U V : ℤ} (hU : 0 < U) (hV : 0 < V)
    (h : U ^ 2 + V ^ 2 = (n : ℤ)) : ((min U V).toNat, (max U V).toNat) ∈ repFinset n := by
  have hmin : 0 < min U V := lt_min hU hV
  have hmax : min U V ≤ max U V := min_le_max
  have hsum : (min U V) ^ 2 + (max U V) ^ 2 = (n : ℤ) := by
    rcases le_total U V with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]; exact h
    · rw [min_eq_right hle, max_eq_left hle]; linarith [h]
  refine mem_repFinset.2 ⟨?_, ?_, ?_⟩
  · simpa using hmin
  · exact Int.toNat_le_toNat hmax
  · have hc : (((min U V).toNat : ℤ)) ^ 2 + (((max U V).toNat : ℤ)) ^ 2 = (n : ℤ) := by
      rw [Int.toNat_of_nonneg hmin.le, Int.toNat_of_nonneg (hmin.le.trans hmax)]
      exact hsum
    exact_mod_cast hc
