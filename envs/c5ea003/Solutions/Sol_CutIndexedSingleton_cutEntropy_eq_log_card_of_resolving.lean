-- Prove2me | solution 1 for CutIndexedSingleton.cutEntropy_eq_log_card_of_resolving
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:28:47.024271+00:00
-- url     : https://prove2.me/submissions/39170189-32b2-45d1-9135-6d769774c62c

-- Sol generated from Novelty/CutIndexedEntropicSingleton.lean
import Mathlib
import Definitions.Def_Novelty_CutIndexedEntropicSingleton
import Definitions.Def_Novelty_CutIndexedEntropy
import Definitions.Def_Novelty_CutIndexedEntropyMono
import Definitions.Def_Novelty_CutIndexedSingleton
import Theorems.Thm_CutIndexedSingleton_cutEntropy_eq_log_of_uniform
import Theorems.Thm_CutIndexedSingleton_cutRank_eq_card_of_minDist
import Theorems.Thm_CutIndexedSingleton_hammingDist_le_of_proj_eq

/-!
# Cut-indexed defects VI: the entropic cut-wise Singleton inequality

File I proved the *counting* cut-wise Singleton inequality
`|C| ≤ q ^ (k - |S|) * cutRank C S`.  File V showed that the entropy profile
`S ↦ cutEntropy C S` is monotone.  This file completes the entropic mirror of the
`CutData` axioms by proving the missing **chain-rule bound**
`H(T) ≤ H(S) + (|T| - |S|) log q`, and deduces the sharpest form of the theory:

`log |C| ≤ H(S) + (k - |S|) log q` for every cut with `|S| ≤ k = n + 1 - d`.

Because `H(S) ≤ log (cutRank C S)` always, this **implies** the counting cut-wise
Singleton inequality and is strictly stronger whenever the marginal on `S` is not
uniform.

## Main results

* `sum_negMulLog_le_group` : the *log-sum / grouping* inequality
  `∑_{i ∈ F} negMulLog pᵢ ≤ negMulLog (∑ pᵢ) + (∑ pᵢ) log N` for `|F| ≤ N`;
* `card_fiber_restrictCut_le` : a pattern on `S` has at most `q ^ (|T| - |S|)`
  extensions to `T`;
* `cutEntropy_le_add_of_subset` : **the entropic one-block growth bound**
  `H(T) ≤ H(S) + (|T| - |S|) log q`;
* `cutEntropy_eq_log_card_of_resolving` : above the Singleton dimension the cut
  entropy is exactly `log |C|`;
* `entropic_cutwise_singleton` : **the entropic cut-wise Singleton inequality**;
* `entropic_cutwise_singleton_implies_counting` : it implies the counting version
  of file I;
* `entropicDefect_nonneg`, `entropicDefect_eq_zero_iff_isMDS` : the entropic cut
  defect is nonnegative, and at the empty cut it vanishes exactly for MDS codes.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 2): every axiom of `CutData` should have an
entropic mirror, and the mirrored Singleton argument should be *strictly sharper*
than the counting one, because entropy sees the shape of the fibre distribution
and rank only sees its support.

Experiment (Experimenter): the mirror is complete.  The one-block growth bound is
the grouping inequality applied fibre-by-fibre, with `N = q ^ (|T| - |S|)` the
number of extensions of a pattern; the proof of the grouping inequality is the
same `log x ≤ x - 1` estimate that powers
`IITTensorNetwork.sum_negMulLog_le_log_card_support`, but *relativised* to a
sub-block, which is what makes it usable inside a sum over cuts.

Analysis (Analyst): the entropic inequality is strictly stronger: for the code
`{000, 100, 010, 110, 001}` of `Examples.pentaCode` the counting bound at
`S = {0}` is not tight while the entropic one records the exact non-uniformity of
the fibres.  The mirror also explains file III: the quantum inequality is a third
member of the same family, with `log (Schmidt rank)` in place of `H(S)`, and it is
the only one of the three that can *fail* to saturate for MDS codes, because of
purity on the complement.

Critique (Critic): the equality analysis at the empty cut needs `2 ≤ q` (for
`q = 1` all logarithms vanish and the criterion is vacuous) and `C.Nonempty`;
`entropicDefect_eq_zero_iff_isMDS` records both.
-/

open Finset

open CutIndexedSingleton

variable {n q : ℕ}

/-! ## The grouping (log-sum) inequality -/


/-! ## Counting the extensions of a pattern -/


/-! ## The entropic chain-rule bound -/


/-! ## The entropic cut-wise Singleton inequality -/








open CutIndexedSingleton in
theorem solution{C : Finset (Word n q)} {d : ℕ}
    (hd : MinDist C d) {T : Finset (Fin n)} (hT : n - T.card < d) (hC : C.Nonempty) :
    cutEntropy C T = Real.log C.card := by
  classical
  have hrank : cutRank C T = C.card := cutRank_eq_card_of_minDist hd hT
  have hinj : Set.InjOn (proj T) (C : Set (Word n q)) := by
    intro x hx z hz hxz
    by_contra hne
    have h1 := hd x hx z hz hne
    have h2 := hammingDist_le_of_proj_eq hxz
    omega
  refine cutEntropy_eq_log_of_uniform (Finset.card_pos.mpr hC) hrank ?_
  intro y hy
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
  have hfib : (fiber C T (proj T c)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨c, ?_⟩
    ext z
    simp only [fiber, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hpz⟩
      exact hinj hz hc hpz
    · rintro rfl
      exact ⟨hc, rfl⟩
  unfold cutProb
  rw [hfib]
  simp
