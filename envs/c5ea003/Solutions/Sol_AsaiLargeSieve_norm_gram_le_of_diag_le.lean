-- Prove2me | solution 1 for AsaiLargeSieve.norm_gram_le_of_diag_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:15:47.738124+00:00
-- url     : https://prove2.me/submissions/1600b558-9bae-453c-b4bd-56ff226af1cc

-- Sol generated from Novelty/AsaiLargeSieveSharp.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiSecondMoment
import Theorems.Thm_AsaiLargeSieve_cauchy_schwarz_sq
/-
# Sharpening the Asai large sieve framework

This file continues the formalisation of the analytic skeleton of the paper
**"On the Second Moment of `L(1/2, As(f) × φ)`"** begun in `Novelty.AsaiLargeSieve`,
`Novelty.AsaiLargeSieveGram`, `Novelty.AsaiSecondMoment` and
`Novelty.AsaiMomentApplications`.  It settles one of the conjectures recorded in
`FUTURE_DIRECTIONS.md` and makes definite progress on a second.

## Conjecture C2 (settled here)

`AsaiLargeSieve.largeSieve_of_periodic_gram` gives the admissible constant `D · (N/q + 1)`
for a Gram matrix supported on `m ≡ n (mod q)` with entries bounded by `D`, and
`largeSieve_of_periodic_gram_dvd` improves this to `D · (N/q)` when `q ∣ N`.  Conjecture C2
asserted that the `+1` is an artefact of the crude counting lemma and that the correct
constant is always `D · ⌈N/q⌉`.  This is proved here:

* `card_congruence_class_le_ceilDiv` — a residue class mod `q` meets `[0,N)` in at most
  `⌈N/q⌉ = (N + q - 1)/q` points (`q ≥ 1`), with `card_congruence_class_ceil_attained`
  an explicit instance showing that this count is attained, so the counting lemma is optimal;
* `largeSieve_of_periodic_gram_ceil` — the resulting large sieve constant `D · ⌈N/q⌉`;
* `ceilDiv_le_div_succ`, `ceilDiv_eq_div_of_dvd`, `ceilDiv_lt_real_of_not_dvd` — the new
  constant is never worse than either previous one, coincides with the divisible-case
  constant when `q ∣ N`, and is *strictly* better than `D · (N/q + 1)` whenever `q ∤ N`;
* `secondMoment_periodic_ceil` — the corresponding second-moment bound.

## Conjecture C1 (partial resolution)

C1 asserted `C_opt ≤ K_Schur ≤ 2 · C_opt`.  The first inequality is
`AsaiLargeSieve.largeSieve_of_schur`.  For the reverse direction we prove here the first
unconditional bound of the right shape:

* `norm_gram_le_geom_mean` — the Gram matrix satisfies the Cauchy–Schwarz entry bound
  `‖G m n‖ ≤ √(G m m) · √(G n n)`; this is positive semidefiniteness of `G`, exactly the
  structural input C1 predicted was the missing ingredient;
* `norm_gram_le_of_diag_le` and `schur_row_le_of_largeSieve` — consequently
  `K_Schur ≤ N · C_opt` for *every* admissible constant `C_opt`;
* `schur_row_le_two_mul_largeSieve_of_dominant` — and if the Gram matrix is diagonally
  dominant on `[0,N)` (the off-diagonal `ℓ¹`-mass of each row is at most its diagonal entry,
  which is the quasi-orthogonality regime `eN ≤ D`), then the conjectured constant is
  correct: `K_Schur ≤ 2 · C_opt`.

So the Schur constant is trapped between `C_opt` and `N · C_opt` in general, and between
`C_opt` and `2 · C_opt` under diagonal dominance; C1 for arbitrary Gram matrices remains
open.

Lab notes (Experimenter).  Counting check for `N = 5`, `q = 2`: the class of `0` in `[0,5)` is
`{0,2,4}`, of size `3 = ⌈5/2⌉`, so the counting lemma is attained.  The gain over the old
criterion is visible in the *real-valued* constants: for `N = 7`, `q = 2` the old constant is
`D · (7/2 + 1) = 4.5 D` while the new one is `D · ⌈7/2⌉ = 4 D`; `ceilDiv_lt_real_of_not_dvd`
proves that a strict gain occurs for every `q ∤ N`.

Critique (Critic).  Is `largeSieve_of_periodic_gram_ceil` vacuous?  No: it strictly implies
both earlier periodic criteria (`ceilDiv_le_div_succ`, `ceilDiv_eq_div_of_dvd`) and its
counting step is attained (`card_congruence_class_ceil_attained`).  Is
`schur_row_le_of_largeSieve` trivial?  No: it goes through the positive semidefiniteness of
the Gram matrix via `AsaiLargeSieve.cauchy_schwarz_sq`; for a general matrix with small
diagonal the off-diagonal entries are completely unconstrained, so no such bound holds.
-/

open Finset Complex

open AsaiLargeSieve

variable {ι : Type*}

/-! ## Positive semidefiniteness of the Gram matrix -/


/-- **Cauchy–Schwarz for the Gram matrix.**  Off-diagonal entries are dominated by the
geometric mean of the two corresponding diagonal entries: this is positive semidefiniteness
of `G` in its most usable elementary form. -/
theorem norm_gram_le_geom_mean (S : Finset ι) (lam : ι → ℕ → ℂ) (m n : ℕ) :
    ‖gram S lam m n‖
      ≤ Real.sqrt (∑ f ∈ S, ‖lam f m‖ ^ 2) * Real.sqrt (∑ f ∈ S, ‖lam f n‖ ^ 2) := by
  have hm : (0 : ℝ) ≤ ∑ f ∈ S, ‖lam f m‖ ^ 2 := Finset.sum_nonneg fun f _ => by positivity
  have hn : (0 : ℝ) ≤ ∑ f ∈ S, ‖lam f n‖ ^ 2 := Finset.sum_nonneg fun f _ => by positivity
  have hcs : ‖gram S lam m n‖ ^ 2
      ≤ (∑ f ∈ S, ‖lam f m‖ ^ 2) * (∑ f ∈ S, ‖lam f n‖ ^ 2) := by
    have := cauchy_schwarz_sq S (fun f => lam f m) (fun f => lam f n)
    simpa [gram] using this
  have hsqrt : ‖gram S lam m n‖
      ≤ Real.sqrt ((∑ f ∈ S, ‖lam f m‖ ^ 2) * (∑ f ∈ S, ‖lam f n‖ ^ 2)) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hcs
  rwa [Real.sqrt_mul hm] at hsqrt



/-! ## Conjecture C2: the ceiling form of the periodic criterion -/










open AsaiLargeSieve in
theorem solution(S : Finset ι) (lam : ι → ℕ → ℂ) (N : ℕ) (D : ℝ)
    (hdiag : ∀ n ∈ Finset.range N, ∑ f ∈ S, ‖lam f n‖ ^ 2 ≤ D)
    {m n : ℕ} (hm : m ∈ Finset.range N) (hn : n ∈ Finset.range N) :
    ‖gram S lam m n‖ ≤ D := by
  have hm0 : (0 : ℝ) ≤ ∑ f ∈ S, ‖lam f m‖ ^ 2 := Finset.sum_nonneg fun f _ => by positivity
  have hD : 0 ≤ D := hm0.trans (hdiag m hm)
  refine (norm_gram_le_geom_mean S lam m n).trans ?_
  have h1 : Real.sqrt (∑ f ∈ S, ‖lam f m‖ ^ 2) ≤ Real.sqrt D :=
    Real.sqrt_le_sqrt (hdiag m hm)
  have h2 : Real.sqrt (∑ f ∈ S, ‖lam f n‖ ^ 2) ≤ Real.sqrt D :=
    Real.sqrt_le_sqrt (hdiag n hn)
  calc Real.sqrt (∑ f ∈ S, ‖lam f m‖ ^ 2) * Real.sqrt (∑ f ∈ S, ‖lam f n‖ ^ 2)
      ≤ Real.sqrt D * Real.sqrt D :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = D := Real.mul_self_sqrt hD
