-- Prove2me | solution 1 for FactoringLab.rat_fiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:55:39.514688+00:00
-- url     : https://prove2.me/submissions/657c7788-1f61-48ac-9fa0-edce01ecdee4

-- Sol generated from Probability/PolynomialCounting.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
import Definitions.Def_Probability_PolynomialCounting
/-
# The Global Polynomial Counting Barrier (Factoring Lab, Phase A v19c — cycle 2)

Closing the **global** half of **Conjecture 1** of `FUTURE_DIRECTIONS.md`.

The previous cycle proved the *per-small-factor* bound
`FactoringLab.polynomial_barrier_counting`: for a fixed prime `p`, a polynomial
`P ∈ ℚ[X]` with `P ≠ C p` returns the correct factor `P(pq) = p` for at most
`deg P` primes `q`.  What was left open was the summation over `p` — the global
count of semiprimes `N = pq ≤ X` on which a fixed polynomial succeeds.

This file closes that step.  The main results are:

* `FactoringLab.successPairs_card_le` — for every `P` with `deg P ≥ 1`,
  the number of pairs `(p, q)` of primes with `p < q`, `pq ≤ X` and
  `P(pq) = p` is at most `deg P · π(√X)`, where `π(√X)` is counted by the
  explicit finset `FactoringLab.smallPrimes X`;
* `FactoringLab.successPairs_card_le_sqrt` — the cruder, hypothesis-free form
  `deg P · (√X + 1)`;
* `FactoringLab.exists_polynomial_failure` — the counting bound turned into an
  existence statement: as soon as the number of semiprimes below `X` exceeds
  `deg P · (√X + 1)`, an explicit semiprime on which `P` fails must exist.  In
  particular the *success density* of any fixed polynomial is `O(√X)` against a
  population of order `X log log X / log X`.

The mechanism is exactly the one predicted in the conjecture: the fibre of the
success set over a fixed small factor `p` injects into the root set of
`P − C p`, and the small factor of a semiprime `≤ X` is at most `√X`.
-/

open FactoringLab

open Finset

/-! ## 1.  The finite populations -/







/-! ## 2.  The smaller factor of a semiprime below `X` is at most `√X` -/


/-! ## 3.  The fibre bound -/


/-! ## 4.  The global counting barrier -/




/-! ## 5.  The counting barrier for rational functions -/







open FactoringLab in
theorem solution(A B : Polynomial ℚ) (X : ℕ) (p : ℕ)
    (hp : p ∈ smallPrimes X) (hAB : A ≠ Polynomial.C (p : ℚ) * B) :
    {z ∈ ratSuccessPairs A B X | z.1 = p}.card ≤ max A.natDegree B.natDegree := by
  classical
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hpp.ne_zero
  set G : Polynomial ℚ := A - Polynomial.C (p : ℚ) * B with hG
  have hG0 : G ≠ 0 := sub_ne_zero.2 hAB
  have hdeg : G.natDegree ≤ max A.natDegree B.natDegree := by
    refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le_max le_rfl ?_)
    exact le_trans (Polynomial.natDegree_mul_le) (by simp)
  set F : Finset (ℕ × ℕ) := {z ∈ ratSuccessPairs A B X | z.1 = p} with hF
  have hmap : ∀ z ∈ F, ((p : ℚ) * (z.2 : ℚ)) ∈ G.roots.toFinset := by
    intro z hz
    have hz1 : z.1 = p := (Finset.mem_filter.1 hz).2
    have heval : A.eval ((z.1 * z.2 : ℕ) : ℚ)
        = (z.1 : ℚ) * B.eval ((z.1 * z.2 : ℕ) : ℚ) :=
      (Finset.mem_filter.1 (Finset.mem_filter.1 hz).1).2
    have hx : ((z.1 * z.2 : ℕ) : ℚ) = (p : ℚ) * (z.2 : ℚ) := by
      rw [Nat.cast_mul, hz1]
    rw [hx, hz1] at heval
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hG0]
    simp only [hG, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_C, heval, sub_self]
  have hinj : ∀ a ∈ F, ∀ b ∈ F,
      (p : ℚ) * (a.2 : ℚ) = (p : ℚ) * (b.2 : ℚ) → a = b := by
    intro a ha b hb hab
    have h2 : a.2 = b.2 := by
      have : (a.2 : ℚ) = (b.2 : ℚ) := mul_left_cancel₀ hpne hab
      exact_mod_cast this
    have ha1 : a.1 = p := (Finset.mem_filter.1 ha).2
    have hb1 : b.1 = p := (Finset.mem_filter.1 hb).2
    exact Prod.ext (ha1.trans hb1.symm) h2
  calc F.card ≤ G.roots.toFinset.card :=
        Finset.card_le_card_of_injOn (fun z => (p : ℚ) * (z.2 : ℚ)) hmap hinj
    _ ≤ Multiset.card G.roots := G.roots.toFinset_card_le
    _ ≤ G.natDegree := G.card_roots'
    _ ≤ max A.natDegree B.natDegree := hdeg
