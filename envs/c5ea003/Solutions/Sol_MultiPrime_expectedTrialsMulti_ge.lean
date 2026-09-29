-- Prove2me | solution 1 for MultiPrime.expectedTrialsMulti_ge
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:34:33.444861+00:00
-- url     : https://prove2.me/submissions/a1536a94-0a89-4d7a-a0af-249551c93c7a

-- Sol generated from Geometry/SingularModuliMultiPrime.lean
import Mathlib
import Definitions.Def_Geometry_SingularModuliMultiPrime
import Theorems.Thm_MultiPrime_density_le
/-
# Singular Moduli Factoring for Arbitrary Composites: it is a *smallest-factor*
# finder

Second research cycle, generalising `SingularModuliBarrier.lean` from semiprimes
`N = p q` to arbitrary squarefree composites `N = p₁ ⋯ p_k`.

Chinese Remainder coordinates now live in `∀ i, ZMod (p i)`, and an evaluation
point `j₀` produces a nontrivial gcd exactly when the reduction of `j₀` is a
root of the class polynomial modulo *some but not all* of the primes.  We prove:

* `MultiPrime.card_goodMulti` — the exact partition identity
  `|G| + ∏ r_i + ∏ (p_i - r_i) = ∏ p_i`;
* `MultiPrime.density_le` — the success density is at most `∑ r_i / p_i`
  (a Weierstrass product inequality, proved here from scratch);
* `MultiPrime.expectedTrialsMulti_ge` — hence the expected number of
  evaluations is at least `p_min / (k d)`, where `d` bounds the number of roots
  of the class polynomial modulo each prime and `p_min` is the *smallest* prime
  factor.

Interpretation.  The `√N` bound for balanced semiprimes is not a coincidence of
the two-prime case: singular moduli factoring is intrinsically a **smallest
prime factor** finder, of the same shape as Pollard rho (`Θ(√p_min)` — better in
the exponent) and Pollard `p-1`.  For balanced semiprimes `p_min ≈ √N` and one
recovers the barrier; for an unbalanced `N` with a small factor the method is
fast for exactly the same, uninteresting, reason that trial division is.

Everything is stated for arbitrary root sets `R i ⊆ ZMod (p i)`; no unproved
property of Hilbert class polynomials is used.
-/

open MultiPrime

open Finset

variable {k : ℕ} {P : Fin k → ℕ} [∀ i, NeZero (P i)]








open MultiPrime in
theorem solution(hk : 0 < k) (R : ∀ i, Finset (ZMod (P i))) (d pmin : ℕ)
    (hd : 0 < d) (hdR : ∀ i, (R i).card ≤ d) (hpmin : ∀ i, pmin ≤ P i)
    (hG : 0 < (goodMulti R).card) :
    (pmin : ℝ) / (k * d) ≤ expectedTrialsMulti R := by
  classical
  have hP : ∀ i, (0:ℝ) < P i := by
    intro i
    have := Nat.pos_of_ne_zero (NeZero.ne (P i)); exact_mod_cast this
  rcases Nat.eq_zero_or_pos pmin with hz | hposmin
  · subst hz
    have hprodpos : (0:ℝ) < ∏ i, (P i : ℝ) := Finset.prod_pos fun i _ => hP i
    have : (0:ℝ) ≤ expectedTrialsMulti R := by
      rw [expectedTrialsMulti]; positivity
    simpa using this
  have hpmin0 : (0:ℝ) < pmin := by exact_mod_cast hposmin
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hG0 : (0:ℝ) < (goodMulti R).card := by exact_mod_cast hG
  have hprodpos : (0:ℝ) < ∏ i, (P i : ℝ) := Finset.prod_pos fun i _ => hP i
  -- each term of the density sum is at most d / pmin
  have hterm : ∀ i, ((R i).card : ℝ) / P i ≤ (d : ℝ) / pmin := by
    intro i
    have h1 : ((R i).card : ℝ) ≤ d := by exact_mod_cast hdR i
    have h2 : (pmin : ℝ) ≤ P i := by exact_mod_cast hpmin i
    calc ((R i).card : ℝ) / P i ≤ (d : ℝ) / P i := by gcongr
      _ ≤ (d : ℝ) / pmin := by gcongr
  have hsum : (∑ i, ((R i).card : ℝ) / P i) ≤ k * ((d : ℝ) / pmin) := by
    calc (∑ i, ((R i).card : ℝ) / P i) ≤ ∑ _i : Fin k, ((d : ℝ) / pmin) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = k * ((d : ℝ) / pmin) := by simp [Finset.sum_const]
  have hdens := density_le hk R
  have hGle : ((goodMulti R).card : ℝ) ≤ (k * ((d:ℝ) / pmin)) * ∏ i, (P i : ℝ) := by
    refine hdens.trans ?_
    exact mul_le_mul_of_nonneg_right hsum (le_of_lt hprodpos)
  rw [expectedTrialsMulti, div_le_div_iff₀ (by positivity) hG0]
  have hGle' : ((goodMulti R).card : ℝ) * pmin ≤ (k * d) * ∏ i, (P i : ℝ) := by
    have := mul_le_mul_of_nonneg_right hGle (le_of_lt hpmin0)
    calc ((goodMulti R).card : ℝ) * pmin
        ≤ ((k * ((d:ℝ) / pmin)) * ∏ i, (P i : ℝ)) * pmin := this
      _ = (k * d) * ∏ i, (P i : ℝ) := by field_simp
  nlinarith [hGle']
