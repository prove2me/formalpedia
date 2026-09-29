-- Prove2me | solution 1 for KTaxonomy.pin_gap_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:47:26.91456+00:00
-- url     : https://prove2.me/submissions/b3261569-dba8-48db-9ef1-e97f2afb6753

-- Sol generated from Cryptography/KTaxonomyGeneralWidth.lean
import Mathlib
import Definitions.Def_Cryptography_KTaxonomyCensusEcon
import Theorems.Thm_KTaxonomy_census_argmin_iff
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

lemma two_pow_pred_kPin_lt {W : ℕ} (hW : 2 ≤ W) : (2:ℝ) ^ (kPin W - 1) < W := by
  have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (x := W) (by omega)
  have h : (2:ℕ) ^ (kPin W - 1) < W := by
    simpa [kPin, Nat.pred_eq_sub_one] using this
  exact_mod_cast h





open KTaxonomy in
theorem solution(W k : ℕ) (hW : 2 ≤ W)
    (hk : ∀ j, census (W : ℝ) k ≤ census (W : ℝ) j) :
    kPin W - k = 1 ∨ kPin W - k = 2 := by
  have hWpos : (0:ℝ) < (W : ℝ) := by exact_mod_cast (show 0 < W by omega)
  obtain ⟨hup, hdown⟩ := (census_argmin_iff (W : ℝ) hWpos k).1 hk
  -- upper bracket: `2 ^ (kPin W - 1) < W ≤ 2 ^ (k + 2)` forces `kPin W ≤ k + 2`
  have h1 : (2:ℝ) ^ (kPin W - 1) < 2 ^ (k + 2) :=
    lt_of_lt_of_le (two_pow_pred_kPin_lt hW) hup
  have h1' : kPin W - 1 < k + 2 := by
    have : (2:ℕ) ^ (kPin W - 1) < 2 ^ (k + 2) := by exact_mod_cast h1
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
  -- lower bracket: `2 ^ (k + 1) ≤ W ≤ 2 ^ kPin W` forces `k + 1 ≤ kPin W`
  have hk1 : 1 ≤ kPin W := one_le_kPin hW
  rcases hdown with hk0 | hlow
  · subst hk0
    -- `k = 0`: then `W ≤ 4` and `W ≥ 2`, so `kPin W ∈ {1, 2}`
    have : kPin W ≤ 2 := by omega
    omega
  · have h2 : (2:ℝ) ^ (k + 1) ≤ 2 ^ kPin W :=
      le_trans hlow (width_le_two_pow_kPin W)
    have h2' : k + 1 ≤ kPin W := by
      have : (2:ℕ) ^ (k + 1) ≤ 2 ^ kPin W := by exact_mod_cast h2
      exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
    omega
