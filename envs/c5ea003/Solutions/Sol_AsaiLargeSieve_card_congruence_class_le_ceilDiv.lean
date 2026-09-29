-- Prove2me | solution 1 for AsaiLargeSieve.card_congruence_class_le_ceilDiv
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:00:51.459347+00:00
-- url     : https://prove2.me/submissions/97bc8d85-78e4-437b-94e9-e29da7d62dd7

-- Sol generated from Novelty/AsaiLargeSieveSharp.lean
import Mathlib
import Definitions.Def_Novelty_AsaiLargeSieve
import Definitions.Def_Novelty_AsaiLargeSieveGram
import Definitions.Def_Novelty_AsaiSecondMoment
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





/-! ## Conjecture C2: the ceiling form of the periodic criterion -/










open AsaiLargeSieve in
theorem solution{q : ℕ} (hq : 0 < q) (N m : ℕ) :
    (((Finset.range N).filter (fun n => m ≡ n [MOD q])).card : ℕ) ≤ (N + q - 1) / q := by
  classical
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  have hceil : (N + q - 1) / q = (N - 1) / q + 1 := by
    have hrw : N + q - 1 = (N - 1) + q := by omega
    rw [hrw, Nat.add_div_right _ hq]
  have h : ((Finset.range N).filter (fun n => m ≡ n [MOD q])).card
      ≤ (Finset.range ((N - 1) / q + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun n => n / q) ?_ ?_
    · intro n hn
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range, Finset.mem_coe] at hn ⊢
      have hle : n / q ≤ (N - 1) / q := Nat.div_le_div_right (by omega)
      omega
    · intro x hx y hy hxy
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hx hy
      have h1 : x % q = y % q := by
        have h2 := hx.2; have h3 := hy.2
        unfold Nat.ModEq at h2 h3
        omega
      have hx' := Nat.div_add_mod x q
      have hy' := Nat.div_add_mod y q
      simp only at hxy
      rw [hxy] at hx'
      omega
  rw [hceil]
  simpa using h
