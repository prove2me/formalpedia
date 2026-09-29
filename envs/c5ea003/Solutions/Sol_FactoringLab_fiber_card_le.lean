-- Prove2me | solution 1 for FactoringLab.fiber_card_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:41:53.556784+00:00
-- url     : https://prove2.me/submissions/25f4ee99-f9a7-42b2-a8a8-6f0c023e5e1e

-- Sol generated from Probability/PolynomialCounting.lean
import Mathlib
import Definitions.Def_Probability_FactoringBarriers
import Definitions.Def_Probability_PolynomialCounting
import Theorems.Thm_FactoringLab_polynomial_barrier_counting
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





theorem mem_semiprimePairs {X : ℕ} {z : ℕ × ℕ} (hz : z ∈ semiprimePairs X) :
    z.1.Prime ∧ z.2.Prime ∧ z.1 < z.2 ∧ z.1 * z.2 ≤ X := (Finset.mem_filter.1 hz).2

theorem mem_successPairs {P : Polynomial ℚ} {X : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ successPairs P X) :
    z.1.Prime ∧ z.2.Prime ∧ z.1 < z.2 ∧ z.1 * z.2 ≤ X ∧
      P.eval ((z.1 * z.2 : ℕ) : ℚ) = (z.1 : ℚ) := by
  obtain ⟨hmem, heval⟩ := Finset.mem_filter.1 hz
  obtain ⟨h1, h2, h3, h4⟩ := mem_semiprimePairs hmem
  exact ⟨h1, h2, h3, h4, heval⟩

/-! ## 2.  The smaller factor of a semiprime below `X` is at most `√X` -/


/-! ## 3.  The fibre bound -/


/-! ## 4.  The global counting barrier -/




/-! ## 5.  The counting barrier for rational functions -/







open FactoringLab in
theorem solution(P : Polynomial ℚ) (hP : 1 ≤ P.natDegree) (X : ℕ) (p : ℕ)
    (hp : p ∈ smallPrimes X) :
    {z ∈ successPairs P X | z.1 = p}.card ≤ P.natDegree := by
  classical
  have hpp : p.Prime := (Finset.mem_filter.1 hp).2
  have hne : P ≠ Polynomial.C (p : ℚ) := by
    intro h
    rw [h, Polynomial.natDegree_C] at hP
    exact absurd hP (by norm_num)
  set F : Finset (ℕ × ℕ) := {z ∈ successPairs P X | z.1 = p} with hF
  set S : Finset ℕ := F.image Prod.snd with hS
  have hcard : F.card = S.card := by
    refine (Finset.card_image_of_injOn ?_).symm
    intro a ha b hb hab
    have ha1 : a.1 = p := (Finset.mem_filter.1 ha).2
    have hb1 : b.1 = p := (Finset.mem_filter.1 hb).2
    exact Prod.ext (ha1.trans hb1.symm) hab
  have hSprop : ∀ q ∈ S, q.Prime ∧ p < q ∧ P.eval ((p * q : ℕ) : ℚ) = (p : ℚ) := by
    intro q hq
    obtain ⟨z, hzF, rfl⟩ := Finset.mem_image.1 hq
    have hz1 : z.1 = p := (Finset.mem_filter.1 hzF).2
    obtain ⟨-, hq2, hlt, -, heval⟩ := mem_successPairs (Finset.mem_filter.1 hzF).1
    refine ⟨hq2, ?_, ?_⟩
    · rwa [hz1] at hlt
    · rw [← hz1]; exact heval
  rw [hcard]
  exact polynomial_barrier_counting P hpp hne S hSprop
