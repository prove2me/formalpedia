-- Prove2me | solution 1 for ErdosProblems.Shared.IdealCounting.card_normSet
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:13:19.241717+00:00
-- url     : https://prove2.me/submissions/d0501562-ec63-4af9-8aa3-6c45ae36384f

import Definitions.Def_ErdosProblems_Shared_IdealCountingEuler
import Mathlib.Analysis.PSeries
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int

/-!
# Counting ideals by their prime factors in a number field

For a number field `K` and a predicate `P` on ideals of `𝓞 K`, `countSupp K P n` is the
number of ideals of absolute norm `n` all of whose prime factors satisfy `P`.  This file
proves the three coefficientwise facts that feed the pole comparison of
`ErdosProblems.Shared.DirichletPole`:

* `card_le_sum_countSupp` (**factorisation into two parts**): every ideal of norm `n` is the
  product of its `P`-part and its `¬P`-part, so the number of ideals of norm `n` is at most the
  Dirichlet convolution of the two restricted counts;
* `sum_countSupp_div_le` (**the bad part converges at `s = 1`**): when `P 𝔭` says that the
  norm of `𝔭` is a prime larger than `N₀`, the series `∑ countSupp K (¬P) n / n` has bounded
  partial sums.  The primes excluded are finitely many primes of small norm and primes of
  norm `p ^ f` with `f ≥ 2`; at most `[K : ℚ]` primes lie over each `p`, so their
  reciprocal norms are dominated by `[K : ℚ] ∑ 1 / p²`, and a finite Euler product over the
  primes involved bounds the whole series;
* `sum_countSupp_mul_le` (**split primes double the count**): if every prime `𝔭` with `P 𝔭`
  has two distinct primes of an extension `M` above it, each of the same norm as `𝔭`, then
  the Dirichlet convolution of the `P`-count with itself is at most the number of ideals of
  `𝓞 M` of norm `n`.  The injection sends a pair of ideals `(I, J)` to the product of the
  first lifts of the prime factors of `I` and the second lifts of those of `J`.
-/

noncomputable section

namespace ErdosProblems.Shared.IdealCounting
open NumberField UniqueFactorizationMonoid Ideal

variable (K : Type*) [Field K] [NumberField K]



theorem natCard_eq_card_filter {α : Type*} (S : Finset α) (p : α → Prop) [DecidablePred p]
    (h : ∀ x, p x → x ∈ S) : Nat.card {x // p x} = (S.filter p).card := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
    simp only [Finset.mem_filter]
    exact ⟨fun hx => ⟨h x hx, hx⟩, fun hx => hx.2⟩)

variable {K}



theorem mem_normSet {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ normSet n ↔ absNorm I = n := by
  simp [normSet]
end ErdosProblems.Shared.IdealCounting

open NumberField UniqueFactorizationMonoid Ideal
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open ErdosProblems in
open ErdosProblems.Shared in
open ErdosProblems.Shared.IdealCounting in
theorem solution (n : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // absNorm I = n} = (normSet (K := K) n).card := by
  classical
  rw [natCard_eq_card_filter (normSet n) (fun I : Ideal (𝓞 K) => absNorm I = n)
    (fun I h => mem_normSet.mpr h)]
  congr 1
  exact Finset.filter_true_of_mem fun I hI => mem_normSet.mp hI
