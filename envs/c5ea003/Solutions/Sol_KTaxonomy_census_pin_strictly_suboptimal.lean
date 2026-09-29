-- Prove2me | solution 1 for KTaxonomy.census_pin_strictly_suboptimal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:47:23.088978+00:00
-- url     : https://prove2.me/submissions/148c3572-cb80-4b0d-9294-a0bb84b5a516

-- Sol generated from Cryptography/KTaxonomyGeneralWidth.lean
import Mathlib
import Definitions.Def_Cryptography_KTaxonomyCensusEcon
import Theorems.Thm_KTaxonomy_census_incr
import Theorems.Thm_KTaxonomy_one_le_kPin

/-!
# The k-taxonomy at general (non-dyadic) support width

`Cryptography.KTaxonomyCensusEcon` settles the taxonomy for dyadic widths `W = 2 ^ m`,
where the census optimum is the exact two-element tie set `{m - 2, m - 1}`.  This file
removes the dyadic restriction: for an arbitrary width `W > 0` it characterises the census
argmin by a pair of *dyadic bracketing inequalities*, and derives from that characterisation
the two structural verdicts of the taxonomy at full generality:

* `census_argmin_iff` : `k` is a census optimum for width `W` iff `W ≤ 2 ^ (k + 2)` and
  (`k = 0` or `2 ^ (k + 1) ≤ W`).  For `W = 2 ^ m` this returns the tie set `{m-2, m-1}`,
  and in general it says the optimum sits at offset `-2` or `-1` relative to `log₂ W`.
* `census_pin_strictly_suboptimal` : for **every** integer width `W ≥ 2` the pin
  `⌈log₂ W⌉` is strictly beaten by `⌈log₂ W⌉ - 1`.  So the pin is never a census optimum —
  not merely for the dyadic widths checked numerically.
* `pin_gap_general` : for **every** integer width `W ≥ 2`, every census optimum `k`
  satisfies `kPin W - k ∈ {1, 2}`.
* `econ_argmin_iff` : the corresponding characterisation for the economics objective,
  obtained for free from the exact anchor identity `econ_eq_census_anchor`.

-- !-- Lab Notes -- !--
Hypothesizer (round 2, after the dyadic results):
 (H6) The `{-2, -1}` offset pattern is not a dyadic accident: it is the general shape of
      the census argmin, expressible as `2 ^ (k+1) ≤ W ≤ 2 ^ (k+2)`.              [BOLD]
 (H7) "Pin is never optimal" holds for every integer width, with a one-line reason:
      `W ≤ 2 ^ ⌈log₂ W⌉` forces the last query to cost more than the residual it saves.
 (H8) The gap `pin - argmin ∈ {1,2}` is a corollary of H6 plus the two clog bracketing
      inequalities `2 ^ (⌈log₂ W⌉ - 1) < W ≤ 2 ^ ⌈log₂ W⌉`, so it needs no case check.

Experimenter: H6–H8 proved below with zero sorries.  The only analytic ingredient is the
increment formula `census W (k+1) - census W k = 1 - W / 2 ^ (k+2)`; everything else is
the discrete-convexity principle `min_of_local_min` from the previous file plus `Nat.clog`
bracketing.

Analyst: the numerically observed statement "gap ∈ {1,2} for every W ≤ 4096" is therefore
not a finite check at all — it is a theorem for every `W`, and the two possible gap values
are exactly the two ends of the census tie bracket.  Nothing in the argument uses dyadicity,
which is the structural reason the tie set has exactly two elements when `W` is dyadic (both
bracketing inequalities become equalities) and one element otherwise.
-/

open KTaxonomy

/-! ## The increment of the census cost -/


/-! ## The census argmin at general width -/



/-! ## The pin is never optimal, at every integer width -/


lemma width_le_two_pow_kPin (W : ℕ) : (W : ℝ) ≤ 2 ^ kPin W := by
  have := Nat.le_pow_clog (b := 2) (by norm_num) W
  exact_mod_cast this






open KTaxonomy in
theorem solution(W : ℕ) (hW : 2 ≤ W) :
    census (W : ℝ) (kPin W - 1) < census (W : ℝ) (kPin W) := by
  have hk1 : 1 ≤ kPin W := one_le_kPin hW
  obtain ⟨p, hp⟩ : ∃ p, kPin W = p + 1 := ⟨kPin W - 1, by omega⟩
  have hpin : (W : ℝ) ≤ 2 ^ (p + 1) := by
    have := width_le_two_pow_kPin W
    rwa [hp] at this
  have hinc := census_incr (W : ℝ) p
  have hpow : (0:ℝ) < 2 ^ (p + 2) := by positivity
  have hhalf : (W : ℝ) / 2 ^ (p + 2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hpow (by norm_num)]
    have : (2:ℝ) ^ (p + 2) = 2 ^ (p + 1) * 2 := by ring
    rw [this]
    linarith
  rw [hp]
  simp only [Nat.add_sub_cancel]
  linarith
