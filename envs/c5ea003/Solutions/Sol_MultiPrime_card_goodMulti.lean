-- Prove2me | solution 1 for MultiPrime.card_goodMulti
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:28:24.746314+00:00
-- url     : https://prove2.me/submissions/f1328249-b242-4bd4-bf58-23043c25cfbf

-- Sol generated from Geometry/SingularModuliMultiPrime.lean
import Mathlib
import Definitions.Def_Geometry_SingularModuliMultiPrime
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
theorem solution(hk : 0 < k) (R : ∀ i, Finset (ZMod (P i))) :
    (goodMulti R).card + (∏ i, (R i).card) + (∏ i, ((R i)ᶜ).card) = ∏ i, P i := by
  classical
  set A : Finset (∀ i, ZMod (P i)) := Fintype.piFinset R with hA
  set B : Finset (∀ i, ZMod (P i)) := Fintype.piFinset (fun i => (R i)ᶜ) with hB
  have hcompl : goodMulti R = (A ∪ B)ᶜ := by
    ext x
    simp only [goodMulti, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.mem_union, hA, hB, Fintype.mem_piFinset, not_or, not_forall]
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      exact ⟨⟨j, hj⟩, ⟨i, by simpa using hi⟩⟩
    · rintro ⟨⟨j, hj⟩, ⟨i, hi⟩⟩
      exact ⟨⟨i, by simpa using hi⟩, ⟨j, hj⟩⟩
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [hA, Fintype.mem_piFinset] at hxA
    rw [hB, Fintype.mem_piFinset] at hxB
    have i0 : Fin k := ⟨0, hk⟩
    exact (Finset.mem_compl.mp (hxB i0)) (hxA i0)
  have hcardA : A.card = ∏ i, (R i).card := by
    rw [hA, Fintype.card_piFinset]
  have hcardB : B.card = ∏ i, ((R i)ᶜ).card := by
    rw [hB, Fintype.card_piFinset]
  have huniv : Fintype.card (∀ i, ZMod (P i)) = ∏ i, P i := by
    rw [Fintype.card_pi]
    exact Finset.prod_congr rfl fun i _ => ZMod.card (P i)
  have := Finset.card_compl (A ∪ B)
  rw [hcompl, this, Finset.card_union_of_disjoint hdisj, hcardA, hcardB, huniv]
  have hle : (∏ i, (R i).card) + (∏ i, ((R i)ᶜ).card) ≤ ∏ i, P i := by
    calc (∏ i, (R i).card) + (∏ i, ((R i)ᶜ).card)
        = A.card + B.card := by rw [hcardA, hcardB]
      _ = (A ∪ B).card := (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ Fintype.card (∀ i, ZMod (P i)) := Finset.card_le_univ _
      _ = ∏ i, P i := huniv
  omega
