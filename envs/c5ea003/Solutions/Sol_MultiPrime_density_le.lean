-- Prove2me | solution 1 for MultiPrime.density_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:31:49.37954+00:00
-- url     : https://prove2.me/submissions/8aca29e6-e97c-4d2f-a56c-6f7608cfbc49

-- Sol generated from Geometry/SingularModuliMultiPrime.lean
import Mathlib
import Definitions.Def_Geometry_SingularModuliMultiPrime
import Theorems.Thm_MultiPrime_card_goodMulti
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



/-- Weierstrass product inequality (proved by induction; used to convert the
partition identity into a union bound on densities). -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
    (h : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.prod_cons]
      have h1 := h a (Finset.mem_cons_self a s)
      have h2 : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1 := fun i hi => h i (Finset.mem_cons_of_mem hi)
      have h3 := ih h2
      have hsum : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg fun i hi => (h2 i hi).1
      nlinarith [h1.1, h1.2, h3, hsum]





open MultiPrime in
theorem solution(hk : 0 < k) (R : ∀ i, Finset (ZMod (P i))) :
    ((goodMulti R).card : ℝ) ≤ (∑ i, ((R i).card : ℝ) / P i) * ∏ i, (P i : ℝ) := by
  classical
  have hP : ∀ i, (0:ℝ) < P i := by
    intro i
    have := Nat.pos_of_ne_zero (NeZero.ne (P i)); exact_mod_cast this
  have hcard := card_goodMulti hk R
  have hrle : ∀ i, ((R i).card : ℝ) ≤ P i := by
    intro i
    have : (R i).card ≤ Fintype.card (ZMod (P i)) := Finset.card_le_univ _
    rw [ZMod.card] at this
    exact_mod_cast this
  have hcompl : ∀ i, (((R i)ᶜ).card : ℝ) = P i - (R i).card := by
    intro i
    have : ((R i)ᶜ).card = Fintype.card (ZMod (P i)) - (R i).card := Finset.card_compl _
    rw [ZMod.card] at this
    have hle : (R i).card ≤ P i := by exact_mod_cast hrle i
    rw [this]
    push_cast [Nat.cast_sub hle]
    ring
  -- pass to real numbers
  have hkey : ((goodMulti R).card : ℝ) + (∏ i, ((R i).card : ℝ)) + (∏ i, (P i - (R i).card : ℝ))
      = ∏ i, (P i : ℝ) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcard
    push_cast at h
    simp only [← hcompl]
    exact h
  set x : Fin k → ℝ := fun i => ((R i).card : ℝ) / P i with hx
  have hx01 : ∀ i ∈ (Finset.univ : Finset (Fin k)), 0 ≤ x i ∧ x i ≤ 1 := by
    intro i _
    constructor
    · positivity
    · rw [hx, div_le_one (hP i)]
      exact hrle i
  have hfac : ∏ i, (P i - (R i).card : ℝ) = (∏ i, (1 - x i)) * ∏ i, (P i : ℝ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hx]
    have hne : (P i : ℝ) ≠ 0 := ne_of_gt (hP i)
    field_simp
  have hw := one_sub_sum_le_prod_one_sub (Finset.univ : Finset (Fin k)) x hx01
  have hprodpos : (0:ℝ) < ∏ i, (P i : ℝ) := Finset.prod_pos fun i _ => hP i
  have hrprod : (0:ℝ) ≤ ∏ i, ((R i).card : ℝ) := Finset.prod_nonneg fun i _ => by positivity
  nlinarith [hkey, hfac, hw, hprodpos, hrprod,
    mul_le_mul_of_nonneg_right hw (le_of_lt hprodpos)]
