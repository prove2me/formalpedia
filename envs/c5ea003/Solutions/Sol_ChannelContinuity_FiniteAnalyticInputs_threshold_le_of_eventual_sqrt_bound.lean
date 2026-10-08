-- Prove2me | solution 1 for ChannelContinuity.FiniteAnalyticInputs.threshold_le_of_eventual_sqrt_bound
-- status  : ACCEPTED   (prove)
-- author  : @JWang226
-- created : 2026-10-07T23:48:21.207249+00:00
-- url     : https://prove2.me/submissions/dfc3ae17-80be-436f-a921-0fbe1450dcf8

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Monotone
import Definitions.Def_CRCD_ChannelContinuity_Main
import Definitions.Def_CRCD_ChannelContinuity_Parameters
import Definitions.Def_CRCD_ChannelContinuity_Testing
import Definitions.Def_CRCD_ChannelContinuity_ThreePiece
import Theorems.Thm_ChannelContinuity_two_term_bound_of_three_piece

section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/









/-!
# The scalar threshold argument

This file formalizes the final real-analysis step in the proof of Theorem 1.
The two-term inequality is the manuscript's equation `eq:contradiction`.
All limits here are proved in Lean; quantum-information input is not postulated
as an axiom and appears explicitly as hypotheses where needed.
-/

open Filter Set
open scoped Topology

namespace ChannelContinuity

/-- When there is a positive rate gap, the cheaper approximation's exponential
factor vanishes as the auxiliary real parameter tends to infinity. -/
private theorem tendsto_two_rpow_neg_gap {dPlus r : ℝ} (hgap : r < dPlus) :
    Tendsto (fun t : ℝ => (2 : ℝ) ^ (-t * (dPlus - r) / 2)) atTop (𝓝 0) := by
  have hlin : Tendsto (fun t : ℝ => (-(dPlus - r) / 2) * t) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by linarith)
  have hexp := (tendsto_rpow_atBot_of_base_gt_one 2 (by norm_num)).comp hlin
  apply hexp.congr
  intro t
  change (2 : ℝ) ^ (-(dPlus - r) / 2 * t) = (2 : ℝ) ^ (-t * (dPlus - r) / 2)
  congr 1
  ring

/-- The small upward perturbation of the higher threshold disappears. -/
private theorem tendsto_two_rpow_inv_two_mul :
    Tendsto (fun t : ℝ => (2 : ℝ) ^ (1 / (2 * t))) atTop (𝓝 1) := by
  have hinv : Tendsto (fun t : ℝ => 1 / (2 * t)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_inv_atTop_zero.const_mul (1 / 2 : ℝ)).congr
      (fun t => by simp [div_eq_mul_inv, mul_inv_rev, mul_comm])
  have hpow := (Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).continuousAt.tendsto.comp hinv
  simpa using hpow

/-- Any exponential with a strictly positive rate vanishes along block sizes. -/
private theorem tendsto_two_rpow_neg_nat_mul {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (2 : ℝ) ^ (-(n : ℝ) * c)) atTop (𝓝 0) := by
  have h := (tendsto_two_rpow_neg_gap (dPlus := 2 * c) (r := 0)
    (by linarith)).comp tendsto_natCast_atTop_atTop
  apply h.congr
  intro n
  change (2 : ℝ) ^ (-(n : ℝ) * (2 * c - 0) / 2) = (2 : ℝ) ^ (-(n : ℝ) * c)
  congr 1
  ring

/-- The high-rate testing estimate implies vanishing at every rate strictly
above the infimum of the order divergences. This is equation `eq:high` used at
`ell > dPlus`; the choice of a suitable order follows from the infimum property. -/
private theorem high_rate_vanishing {E : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {ell : ℝ}
    (hnonneg : ∀ n, 0 ≤ E n ell)
    (hell : sInf (f '' Ioi 1) < ell)
    (htesting : ∀ a : ℝ, 1 < a → f a < ell → ∀ n : ℕ, 0 < n →
      E n ell ≤ (2 : ℝ) ^ (-(n : ℝ) * (a - 1) * (ell - f a))) :
    Tendsto (fun n => E n ell) atTop (𝓝 0) := by
  have hne : (f '' Ioi (1 : ℝ)).Nonempty := ⟨f 2, 2, by norm_num, rfl⟩
  obtain ⟨_, ⟨a, ha, rfl⟩, hfa⟩ := exists_lt_of_csInf_lt hne hell
  have hdecay : Tendsto
      (fun n : ℕ => (2 : ℝ) ^ (-(n : ℝ) * (a - 1) * (ell - f a)))
      atTop (𝓝 0) := by
    simpa only [mul_assoc] using
      (tendsto_two_rpow_neg_nat_mul (mul_pos (sub_pos.mpr ha) (sub_pos.mpr hfa)))
  apply squeeze_zero' (Eventually.of_forall hnonneg) _ hdecay
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact htesting a ha hfa n (by omega)

/-- The manuscript's last limit, with no uniformity in the earlier block-size
limit assumed: only the already-established inequality at each fixed `t` is used. -/
private theorem threshold_le_of_two_term_bound {dPlus r b : ℝ} (hb : b < 1)
    (hbound : ∀ t : ℝ, 1 ≤ t →
      1 ≤ (1 + b) * (2 : ℝ) ^ (-t * (dPlus - r) / 2) +
        b * (2 : ℝ) ^ (1 / (2 * t))) :
    dPlus ≤ r := by
  by_contra h
  have hgap : r < dPlus := lt_of_not_ge h
  have hlim : Tendsto (fun t : ℝ =>
      (1 + b) * (2 : ℝ) ^ (-t * (dPlus - r) / 2) +
        b * (2 : ℝ) ^ (1 / (2 * t))) atTop (𝓝 b) := by
    simpa using ((tendsto_two_rpow_neg_gap hgap).const_mul (1 + b)).add
      (tendsto_two_rpow_inv_two_mul.const_mul b)
  have hb' : 1 ≤ b := ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht using hbound t ht)
  exact (not_le_of_gt hb) hb'













end ChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/





/-!
# Parameters and scalar normalization in the three-piece estimate

This file verifies the order choice `α = n / (n - t)` and the base-two
power algebra used to normalize the exponentiated Schatten bound.
-/

namespace ChannelContinuity









/-- Raising a block-rate weight to `s/2`, with `s=t/n`, cancels the block size. -/
private theorem block_rate_weight {n : ℝ} (hn : n ≠ 0) (t rate : ℝ) :
    ((2 : ℝ) ^ (n * rate)) ^ (t / n / 2) = (2 : ℝ) ^ (t * rate / 2) := by
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  field_simp

/-- Dividing the cheaper piece by the threshold's exponential gives a negative
rate-gap factor. -/
private theorem normalized_low_weight {n : ℝ} (hn : n ≠ 0) (t r dPlus : ℝ) :
    ((2 : ℝ) ^ (n * r)) ^ (t / n / 2) / (2 : ℝ) ^ (t * dPlus / 2) =
      (2 : ℝ) ^ (-t * (dPlus - r) / 2) := by
  rw [block_rate_weight hn, ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

/-- The fixed multiplier four becomes the factor `2^(t/n)`. -/
private theorem four_weight (n t : ℝ) :
    (4 : ℝ) ^ (t / n / 2) = (2 : ℝ) ^ (t / n) := by
  rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- General normalized weight for a piece with CP multiplier four. -/
private theorem normalized_four_weight {n : ℝ} (hn : n ≠ 0) (t rate dPlus : ℝ) :
    ((4 : ℝ) * (2 : ℝ) ^ (n * rate)) ^ (t / n / 2) /
        (2 : ℝ) ^ (t * dPlus / 2) =
      (2 : ℝ) ^ (t / n) * (2 : ℝ) ^ (t * (rate - dPlus) / 2) := by
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg (by norm_num) _),
    four_weight, block_rate_weight hn, mul_div_assoc,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 2
  ring

/-- The higher approximation rate `dPlus+t⁻²` leaves only `2^(1/(2t))`. -/
private theorem normalized_high_weight {n t : ℝ} (hn : n ≠ 0) (ht : t ≠ 0) (dPlus : ℝ) :
    ((4 : ℝ) * (2 : ℝ) ^ (n * (dPlus + 1 / (t * t)))) ^ (t / n / 2) /
        (2 : ℝ) ^ (t * dPlus / 2) =
      (2 : ℝ) ^ (t / n) * (2 : ℝ) ^ (1 / (2 * t)) := by
  rw [normalized_four_weight hn]
  congr 2
  field_simp
  ring



/-- Exact normalization of all three terms, including both factors arising
from the fixed multiplier four. -/
private theorem raw_schatten_normalization {n : ℕ} {t : ℝ}
    (hn : (n : ℝ) ≠ 0) (ht : t ≠ 0) (r dPlus cap b ε : ℝ) :
    rawSchattenRhs n t r dPlus cap b ε / (2 : ℝ) ^ (t * dPlus / 2) =
      threePieceRhs n t r dPlus cap b ε := by
  unfold rawSchattenRhs threePieceRhs
  rw [add_div, add_div,
    mul_div_assoc ((1 + b) ^ (1 - t / (n : ℝ))) _ _,
    mul_div_assoc ((b + ε) ^ (1 - t / (n : ℝ))) _ _,
    mul_div_assoc (ε ^ (1 - t / (n : ℝ))) _ _,
    normalized_low_weight hn, normalized_high_weight hn ht, normalized_four_weight hn]
  ring

/-- The raw three-term Schatten estimate implies the normalized inequality
used by the first limiting argument.  This step is scalar algebra only; the
raw operator-theoretic estimate remains an explicit hypothesis. -/
private theorem three_piece_bound_of_raw_schatten {n : ℕ} {t r dPlus cap b ε : ℝ}
    (ht : 1 ≤ t) (htn : t < (n : ℝ))
    (hraw : (2 : ℝ) ^ (t * dPlus / 2) ≤ rawSchattenRhs n t r dPlus cap b ε) :
    1 ≤ threePieceRhs n t r dPlus cap b ε := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (lt_trans ht0 htn)
  have hden : 0 < (2 : ℝ) ^ (t * dPlus / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hdiv : 1 ≤ rawSchattenRhs n t r dPlus cap b ε / (2 : ℝ) ^ (t * dPlus / 2) :=
    (le_div_iff₀ hden).2 (by simpa using hraw)
  simpa [raw_schatten_normalization hn0 (ne_of_gt ht0)] using hdiv

end ChannelContinuity

end


section

/-
Copyright (c) 2026 Jinzhao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinzhao Wang (AI-assisted formalization)
-/










/-!
# Scalar limit argument for Theorem 1

The successive limit passages, testing-threshold argument, and left/right
assembly are proved. `FiniteAnalyticInputs` records the scalar estimates needed
for the finite right-limit argument; its raw Schatten estimate is normalized
here. `QuantumChannelContinuity.QuantumMain` derives that estimate from the
proved operator bounds, and `QuantumChannelContinuity.ContinuityAssembly`
constructs the input record for concrete channels in the finite branch.
`QuantumChannelContinuity.Main` combines the finite and infinite cases with
the proved state-order facts to export the unconditional channel theorem.
-/

open Filter Set
open scoped Topology ENNReal

namespace ChannelContinuity



/-- Derive the normalized estimate, including the eventually valid condition
`n > t`, from the raw exponentiated Schatten hypothesis. -/
private theorem FiniteAnalyticInputs.three_piece (h : FiniteAnalyticInputs)
    (r : ℝ) (hr : 0 ≤ r) (hgap : r < sInf (h.renyi '' Ioi 1))
    (t : ℝ) (ht : 1 ≤ t) : ∀ᶠ n : ℕ in atTop,
      1 ≤ threePieceRhs n t r (sInf (h.renyi '' Ioi 1)) h.cap
        (Real.sqrt (h.testing n r))
        (Real.sqrt (h.testing n (sInf (h.renyi '' Ioi 1) + 1 / (t * t)))) := by
  have hn : ∀ᶠ n : ℕ in atTop, 2 * t < (n : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually
      (eventually_gt_atTop (2 * t))
  filter_upwards [hn] with n h2tn
  have htn : t < (n : ℝ) := by linarith
  exact three_piece_bound_of_raw_schatten ht htn
    (h.raw_schatten r hr hgap t ht n htn h2tn.le)

end ChannelContinuity

open ChannelContinuity

open ChannelContinuity in
/-- Amplification from a fixed eventual error strictly below one, with both
successive limits checked. -/
theorem solution
    (h : FiniteAnalyticInputs) {r B : ℝ} (hr : 0 ≤ r) (hBlt : B < 1)
    (hBevent : ∀ᶠ n in atTop, Real.sqrt (h.testing n r) ≤ B) :
    sInf (h.renyi '' Ioi 1) ≤ r := by
  by_cases hdone : sInf (h.renyi '' Ioi 1) ≤ r
  · exact hdone
  have hgap : r < sInf (h.renyi '' Ioi 1) := lt_of_not_ge hdone
  apply threshold_le_of_two_term_bound hBlt
  intro t ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hell : sInf (h.renyi '' Ioi 1) <
      sInf (h.renyi '' Ioi 1) + 1 / (t * t) :=
    lt_add_of_pos_right _ (by positivity)
  have hhigh := high_rate_vanishing
    (fun n => h.testing_nonneg n _) hell
    (fun a ha haell n hn => h.renyi_testing a ha _ haell n hn)
  have hsqrt : Tendsto
      (fun n => Real.sqrt (h.testing n (sInf (h.renyi '' Ioi 1) + 1 / (t * t))))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hhigh
  exact two_term_bound_of_three_piece
    (fun n => Real.sqrt_nonneg _) (fun n => Real.sqrt_nonneg _)
    hBevent hsqrt (h.three_piece r hr hgap t ht)

end
