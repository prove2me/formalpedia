-- Prove2me | solution 1 for Logic.JFeature.one_le_maxRatioStat
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:13:34.074201+00:00
-- url     : https://prove2.me/submissions/f3ec5131-78bb-4f1f-912e-de2f812ee77a

-- Sol generated from Logic/JFeatureSweepSynthesis.lean
import Mathlib
import Definitions.Def_Logic_JFeatureMarginalBlindness
import Definitions.Def_Logic_JFeatureMaxStatistic
import Definitions.Def_Logic_JFeatureSweepSynthesis
import Definitions.Def_Logic_PhaseRouteAlignment
import Theorems.Thm_Logic_JFeature_exists_fiber_rate_ge_globalRate
/-
# Synthesis: what a flat j-feature sweep does and does not establish

This file ties together the three strands of the paper-248 analysis.

* `pval_maxRatio_eq_one` : the **uncalibrated** scan statistic
  `max_k rate(cell k) / globalRate` is `≥ 1` on *every* draw of the null
  ensemble (pigeonhole, `Logic.JFeature.exists_fiber_rate_ge_globalRate`), so the
  naive test "the best cell exceeds the global rate" has permutation p-value
  exactly `1`.  Only a max-statistic calibration can say anything.
* `sweep_blindness_two_views` : a carrier living in the *joint* structure is
  invisible to marginal features in **two independent statistical views** — the
  contingency view (enrichment ratio exactly `1`, this development) and the
  regression view (degree-1 `R² ≤ 0`, `Logic.PhaseRoute.Rsq_additive_nonpos`).
  Flatness of a marginal sweep is therefore a property of the *test*, not
  evidence about the carrier.
-/

open Logic.JFeature

open Finset


variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]






open Logic.PhaseRoute

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable [Nonempty α] [Nonempty β]





open Logic.JFeature in
omit [Fintype Ω] [Nonempty Ω] in
theorem solution(u : ι → κ) (Hs : Ω → Finset ι)
    (hκ : (univ : Finset κ).Nonempty) (hne : ∀ w, (Hs w).Nonempty) (w : Ω) :
    1 ≤ maxRatioStat u Hs hκ w := by
  obtain ⟨k, _, hk⟩ := exists_fiber_rate_ge_globalRate u (Hs w)
  have hg : 0 < globalRate (Hs w) := by
    have h1 : 0 < ((Hs w).card : ℝ) := by
      have : 0 < (Hs w).card := Finset.card_pos.2 (hne w)
      exact_mod_cast this
    have h2 : (0:ℝ) < (Fintype.card ι : ℝ) := by
      have : 0 < Fintype.card ι := Fintype.card_pos
      exact_mod_cast this
    unfold globalRate; positivity
  have h1 : (1:ℝ) ≤ rate (Hs w) (univ.filter (fun i => u i = k)) / globalRate (Hs w) := by
    rw [le_div_iff₀ hg, one_mul]
    exact hk
  refine le_trans h1 ?_
  rw [maxRatioStat]
  exact Finset.le_sup' (f := fun k =>
    rate (Hs w) (univ.filter (fun i => u i = k)) / globalRate (Hs w)) (Finset.mem_univ k)
