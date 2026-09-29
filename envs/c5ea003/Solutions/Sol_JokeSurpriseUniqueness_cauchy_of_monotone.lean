-- Prove2me | solution 1 for JokeSurpriseUniqueness.cauchy_of_monotone
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:38:55.942529+00:00
-- url     : https://prove2.me/submissions/83878a71-3178-4d7e-bdbb-5f61c3ca1ad3

-- Sol generated from Applications/JokeSurpriseUniqueness.lean
import Mathlib
import Definitions.Def_Applications_JokeSurpriseStability
import Definitions.Def_Applications_JokeSurpriseUniqueness

/-!
# Why *this* invariant? A uniqueness theorem for surprise

The two preceding files of this thread take the formula `humor S = max' S - min' S`
(equivalently `Metric.diam S`, by `JokeSurpriseStability.humor_eq_diam`) as given, and
study its algebra (`Applications.JokeSurpriseAlgebra`,
`Applications.JokeColimitUniversality`) and its stability
(`Applications.JokeSurpriseStability`). The obvious objection is that the formula is
*chosen*: any monotone functional on setups would produce a plausible-looking theory.

This file removes the choice. We axiomatise what a *humor scale* must satisfy —

* **position blindness**: a joke is not funnier for being told about larger numbers
  (translation invariance);
* **staged telling**: telling a joke in two consecutive stages accumulates the surprise
  of the stages (concatenation additivity);
* **monotonicity**: widening the gap between the extreme readings cannot reduce
  surprise —

and prove that these three axioms pin the invariant down **completely**:

* `HumorScale.eq_scale_mul` : every humor scale is `V m M = c · (M - m)` with
  `c = V 0 1`;
* `HumorScale.scale_nonneg` : the constant is nonnegative;
* `HumorScale.eq_scale_mul_humor` : on setups, every humor scale is a nonnegative
  multiple of the catalog's `humor`;
* `HumorScale.ext_of_scale_eq` : a humor scale is determined by its value on the unit
  gap — the theory has exactly one degree of freedom, the choice of unit.

Consequently every theorem of the thread transfers automatically to *any* admissible
invariant, without re-proof:

* `HumorScale.submodular` : every humor scale is submodular;
* `HumorScale.lipschitz_hausdorff` : every humor scale is `2c`-Lipschitz for the
  Hausdorff distance between setups.

The technical heart is `cauchy_of_monotone`: a monotone solution of the Cauchy
functional equation on `[0, ∞)` is linear. It is proved from scratch (rational
dilations `g (k s) = k g s`, the floor sandwich `k/n ≤ t ≤ (k+1)/n`, and an
Archimedean limit), since a monotone — as opposed to continuous or measurable —
Cauchy theorem is not available off the shelf.

-- !-- Lab Notes -- !--
Hypothesis (H7): the range/diameter formula is not a modelling choice but is *forced*
by position blindness, staged telling, and monotonicity.
Hypothesis (H8): if H7 holds, the whole thread (submodularity, Hausdorff stability) is
axiom-independent and transfers to every admissible invariant.

Experiment: H7 was reduced to a Cauchy functional equation for `g t = V 0 t` on
`[0, ∞)`. The additivity `g (s + t) = g s + g t` comes from concatenation plus
translation invariance; monotonicity of `g` from the third axiom. The linearity
`g t = g 1 · t` was then proved by hand: `g (k s) = k g s` by induction, hence
`g (1/n) = g 1 / n` and `g (k/n) = g 1 · k / n`; sandwiching `t` between
`⌊n t⌋/n` and `(⌊n t⌋ + 1)/n` gives `|g t - g 1 · t| ≤ g 1 / n` for every `n`, and the
Archimedean property finishes. Non-vacuity was checked by exhibiting the range scale
`rangeScale` (with `c = 1`) as a model of the axioms.

Analysis: H7 and H8 both survive, and they retro-justify the earlier files: every
theorem previously proved about `humor` is a theorem about *any* invariant obeying the
three axioms, up to the scale factor `c`.

Critique: monotonicity is essential and not decorative — without it, a Hamel-basis
solution of the Cauchy equation gives a wildly discontinuous "humor scale" that is
translation invariant and concatenation additive but not proportional to the range.
The axioms are consistent (`rangeScale`) and, by `ext_of_scale_eq`, categorical up to
the single scale parameter.

Synthesis: surprise is the unique — up to choice of unit — position-blind, stage-
additive, monotone measure of a setup; the range formula of the catalog is its
normalisation at `c = 1`.
-/

open Finset Metric JokeSurpriseAlgebra JokeSurpriseStability

open JokeSurpriseUniqueness

/-! ### A monotone Cauchy equation -/


/-! ### Humor scales -/


open HumorScale

variable (V : HumorScale)












open JokeSurpriseUniqueness in
theorem solution(g : ℝ → ℝ)
    (hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → g (s + t) = g s + g t)
    (hmono : ∀ s t : ℝ, 0 ≤ s → s ≤ t → g s ≤ g t) :
    ∀ t : ℝ, 0 ≤ t → g t = g 1 * t := by
  have hzero : g 0 = 0 := by have := hadd 0 0 le_rfl le_rfl; simp at this; linarith
  have hnsmul : ∀ (k : ℕ) (s : ℝ), 0 ≤ s → g (k * s) = k * g s := by
    intro k s hs
    induction k with
    | zero => simpa using hzero
    | succ n ih =>
        have h1 : ((n : ℝ) + 1) * s = (n : ℝ) * s + s := by ring
        push_cast
        rw [h1, hadd _ _ (by positivity) hs, ih]
        ring
  have hc : 0 ≤ g 1 := by have := hmono 0 1 le_rfl (by norm_num); linarith
  intro t ht
  by_contra hne
  have hkey : ∀ n : ℕ, 0 < n → |g t - g 1 * t| ≤ g 1 / n := by
    intro n hn
    have hnR : (0:ℝ) < n := by exact_mod_cast hn
    set k : ℕ := ⌊(n : ℝ) * t⌋₊ with hk
    have hkt : (k : ℝ) / n ≤ t := by
      rw [div_le_iff₀ hnR]
      have := Nat.floor_le (by positivity : (0:ℝ) ≤ (n:ℝ) * t)
      nlinarith
    have htk : t ≤ ((k : ℝ) + 1) / n := by
      rw [le_div_iff₀ hnR]
      have := Nat.lt_floor_add_one ((n : ℝ) * t)
      nlinarith
    have hginv : g (1 / n) = g 1 / n := by
      have h3 : g ((n : ℝ) * (1 / n)) = n * g (1 / n) := hnsmul n (1/n) (by positivity)
      rw [mul_one_div, div_self (ne_of_gt hnR)] at h3
      field_simp at h3 ⊢
      linarith
    have hgk : g ((k : ℝ) / n) = g 1 * k / n := by
      have h2 : ((k : ℝ) / n) = (k : ℝ) * (1 / n) := by ring
      rw [h2, hnsmul k (1/n) (by positivity), hginv]
      ring
    have hgk1 : g (((k : ℝ) + 1) / n) = g 1 * ((k : ℝ) + 1) / n := by
      have h2 : (((k : ℝ) + 1) / n) = ((k + 1 : ℕ) : ℝ) * (1 / n) := by push_cast; ring
      rw [h2, hnsmul (k+1) (1/n) (by positivity), hginv]
      push_cast; ring
    have hlow : g 1 * (k : ℝ) / n ≤ g t := by
      rw [← hgk]; exact hmono _ _ (by positivity) hkt
    have hhigh : g t ≤ g 1 * ((k : ℝ) + 1) / n := by
      rw [← hgk1]; exact hmono _ _ ht htk
    have hkt' : g 1 * (k : ℝ) / n ≤ g 1 * t := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hkt hc
    have htk' : g 1 * t ≤ g 1 * ((k : ℝ) + 1) / n := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left htk hc
    have hdiff : g 1 * ((k : ℝ) + 1) / n - g 1 * (k : ℝ) / n = g 1 / n := by
      field_simp; ring
    rw [abs_le]
    constructor <;> linarith
  have hpos : 0 < |g t - g 1 * t| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (g 1 / |g t - g 1 * t|)
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      have hnn : 0 ≤ g 1 / |g t - g 1 * t| := div_nonneg hc (le_of_lt hpos)
      simp at hn
      linarith
    · exact h
  have hb := hkey n hn0
  have hnR : (0:ℝ) < n := by exact_mod_cast hn0
  rw [div_lt_iff₀ hpos] at hn
  rw [le_div_iff₀ hnR] at hb
  linarith
