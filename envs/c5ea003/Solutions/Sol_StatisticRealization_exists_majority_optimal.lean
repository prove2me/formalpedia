-- Prove2me | solution 1 for StatisticRealization.exists_majority_optimal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:50:32.26848+00:00
-- url     : https://prove2.me/submissions/9b313880-5ed7-4c33-822b-0c808fbcc664

-- Sol generated from Novelty/StatisticRealizationBound.lean
import Mathlib
import Definitions.Def_Novelty_OracleRealizationGap
import Definitions.Def_Novelty_StatisticRealizationBound

/-!
# Crediting a sensor to a statistic: the exact realization bound

The round-74 experiment credited a policy with *realizing* an oracle sensor by comparing its
predictions to the sensor on a labelled population, first pooled ("lenient") and then inside
`log N` strata ("strict").  The strict verdict was `0 %` for every `N`-only policy.

This file supplies the exact combinatorial law behind such crediting.  Fix a finite population
`P`, a **statistic** `T : ι → κ` (everything a policy is allowed to read: residues, magnitude
stratum, a menu of probe answers, …) and a Boolean **target** `s : ι → Bool` (the sensor).  A
`T`-measurable policy is a map `f : κ → Bool`, and its error count is `err P T s f`.

## Main results

* `err_ge_irredError` : every `T`-measurable policy makes at least
  `irredError P T s = ∑_classes min(#true, #false)` mistakes;
* `exists_majority_optimal` : the class-wise majority vote attains that value exactly;
* `isLeast_err` : hence `irredError P T s` **is** the minimum error — a measurement, not a bound;
* `two_mul_irredError_of_balanced` : if every `T`-class is balanced (`#true = #false`), the
  minimum error is exactly half the population: the statistic realizes *nothing*, which is the
  exact form of the "strict within-strata crediting `0 %`" verdict;
* `residue_err_pos` : instantiated at the navigation sensor of
  `Novelty.OracleRealizationGap`, every residue-only policy has strictly positive error on an
  explicit two-point semiprime population, for every modulus and every threshold.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): "percentage of the oracle peak realized" is not an information-theoretic
primitive; it is a minimum-error functional of the statistic the policy is allowed to read, and
it should have a closed form.

Experiment (Experimenter): `ComputationalEvidence.md` enumerates small populations (`|P| ≤ 8`)
and all `2^|κ|` policies by brute force, checking `min_f err = ∑ minorities` in every case.

Analysis (Analyst): the closed form is the sum of class minorities.  Two extremes explain the
two crediting regimes measured in the lab: statistics whose classes are pure give minimum error
`0` (full realization), and statistics whose classes are balanced give minimum error `|P| / 2`
(zero realization, no matter how the policy is fitted).  The lenient pooled credit sits between
because pooling merges strata whose base rates differ.

Critique (Critic): the bound must be attained, else "0 %" would be an artefact of a weak
argument; `exists_majority_optimal` exhibits the optimal policy explicitly.  The theorem is
stated for arbitrary `κ`, so it applies verbatim to menu-answer vectors, not just residues.
-/

open StatisticRealization

open Finset

variable {ι κ : Type*} [DecidableEq κ]




/-- Restricting the mismatch set to a `T`-class replaces `f (T i)` by the constant `f c`. -/
lemma class_restrict (P : Finset ι) (T : ι → κ) (s : ι → Bool) (f : κ → Bool) (c : κ) :
    ((P.filter fun i => f (T i) ≠ s i).filter fun i => T i = c)
      = (P.filter fun i => T i = c).filter fun i => f c ≠ s i := by
  rw [Finset.filter_filter, Finset.filter_filter]
  apply Finset.filter_congr
  intro i _
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by rw [← h2]; exact h1⟩
  · rintro ⟨h2, h1⟩; exact ⟨by rw [h2]; exact h1, h2⟩

/-- On a class where the policy answers `true`, its errors are the `false`-labelled members. -/
lemma err_class_true (P : Finset ι) (T : ι → κ) (s : ι → Bool) (f : κ → Bool) {c : κ}
    (hfc : f c = true) :
    ((P.filter fun i => f (T i) ≠ s i).filter fun i => T i = c).card =
      ((P.filter fun i => T i = c).filter fun i => s i = false).card := by
  rw [class_restrict]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [hfc]
  cases s i <;> simp

/-- On a class where the policy answers `false`, its errors are the `true`-labelled members. -/
lemma err_class_false (P : Finset ι) (T : ι → κ) (s : ι → Bool) (f : κ → Bool) {c : κ}
    (hfc : f c = false) :
    ((P.filter fun i => f (T i) ≠ s i).filter fun i => T i = c).card =
      ((P.filter fun i => T i = c).filter fun i => s i = true).card := by
  rw [class_restrict]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [hfc]
  cases s i <;> simp

/-- The class-wise decomposition of the error count. -/
lemma err_eq_sum (P : Finset ι) (T : ι → κ) (s : ι → Bool) (f : κ → Bool) :
    err P T s f = ∑ c ∈ P.image T,
      ((P.filter fun i => f (T i) ≠ s i).filter fun i => T i = c).card := by
  refine Finset.card_eq_sum_card_fiberwise ?_
  intro i hi
  exact Finset.mem_image_of_mem T (Finset.mem_of_mem_filter i hi)







/-! ## The navigation sensor against residue statistics -/

open OracleRealizationGap



open StatisticRealization in
theorem solution(P : Finset ι) (T : ι → κ) (s : ι → Bool) :
    err P T s (majority P T s) = irredError P T s := by
  rw [err_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro c _
  unfold minority
  by_cases h : ((P.filter fun i => T i = c).filter fun i => s i = false).card ≤
      ((P.filter fun i => T i = c).filter fun i => s i = true).card
  · have hmaj : majority P T s c = true := by unfold majority; simpa using h
    rw [err_class_true P T s _ hmaj]
    exact (min_eq_right h).symm
  · have hmaj : majority P T s c = false := by unfold majority; simpa using h
    rw [err_class_false P T s _ hmaj]
    exact (min_eq_left (le_of_lt (lt_of_not_ge h))).symm
