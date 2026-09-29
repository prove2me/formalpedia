-- Prove2me | solution 1 for KServer.race_gain_bound2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T20:12:53.81913+00:00
-- url     : https://prove2.me/submissions/101cc5e7-4020-4b8d-a61b-1cbf6af2f7f6

import Mathlib
import Definitions.Def_KServer_race_core
import Definitions.Def_KServer_race_gain
import Definitions.Def_KServer_race_pad
import Definitions.Def_KServer_discrete_martingale
import Theorems.Thm_KServer_martingale_abs_anticoncentration

set_option maxHeartbeats 3200000

namespace KServer

open Race

theorem race_gain_bound2 {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) (hcB : 0 ≤ cB)
    {cLo' : ℝ} (hεLo : ε ≤ cLo') (hLocB : cLo' ≤ cB + ε)
    {Nb : ℝ} (hNb : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * Nbad A BL BR CC κ cLo' ω ≤ Nb) :
    Real.sqrt (((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
          + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2)))
      - (κ : ℝ) * ε - (cB + ε + cLo') * Nb
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| := by
  have hLo0 : (0 : ℝ) ≤ cLo' := le_trans hε.le hεLo
  have hRP0 : ∀ ω : RΩ A BL BR CC κ, 0 ≤ RP A BL BR CC κ ε ω :=
    fun ω => (RP_pos A BL BR CC κ ε hε ω).le
  have hE0 : 0 ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| :=
    Finset.sum_nonneg fun ω _ => mul_nonneg (hRP0 ω) (abs_nonneg _)
  have hNb0 : (0 : ℝ) ≤ Nb :=
    le_trans (Finset.sum_nonneg fun ω _ => mul_nonneg (hRP0 ω)
      (Nbad_nonneg A BL BR CC κ cLo' ω)) hNb
  have hc0 : (0 : ℝ) ≤ cB + ε + cLo' := by linarith [hε.le]
  by_cases hκ0 : κ = 0
  · subst hκ0
    simp only [Nat.cast_zero, zero_mul]
    norm_num
    nlinarith
  · have hκ1 : (1 : ℝ) ≤ (κ : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hκ0
    have hγpos : (0 : ℝ) < cB + ε := by linarith
    have hCpos : (0 : ℝ) < 8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
        + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2) := by
      have h1 : (0 : ℝ) < (κ : ℝ) * (cB + ε) ^ 2 := by
        have := pow_pos hγpos 2
        nlinarith
      nlinarith [sq_nonneg ((κ : ℝ) * (cB + ε) ^ 2), pow_pos hγpos 2]
    haveI : DecidableEq (PΩ A BL BR CC κ) := Classical.decEq _
    have hanti := martingale_abs_anticoncentration
      (PP A BL BR CC κ ε) κ (phist A BL BR CC κ)
      (pX A BL BR CC κ ε cLo') (pV A BL BR CC κ ε cLo')
      (pad_martingale A BL BR CC κ ε cLo' hε)
      (cB + ε) ((κ : ℝ) * (cB + ε) ^ 2) ((κ : ℝ) * cLo' ^ 2)
      hγpos.le
      (fun j _ p => pX_abs_le A BL BR CC κ ε cLo' hε hcB hLo0 hLocB j p)
      (fun j _ p => pV_nonneg A BL BR CC κ ε cLo' hε j p)
      (fun p => pV_total_le A BL BR CC κ ε cLo' hε hcB hLo0 hLocB p)
      (fun p => pV_total_ge A BL BR CC κ ε cLo' hε hεLo p)
      (by positivity) (by positivity)
      (PP_sum A BL BR CC κ ε hε)
    have hred := pad_gain_reduce A BL BR CC κ ε cLo' hε hcB hLo0 hNb
    have hm0 : 0 ≤ ∑ p : PΩ A BL BR CC κ, PP A BL BR CC κ ε p
        * |mgSum (pX A BL BR CC κ ε cLo') κ p| :=
      Finset.sum_nonneg fun p _ => mul_nonneg
        (PP_pos A BL BR CC κ ε hε p).le (abs_nonneg _)
    have h2 : (∑ p : PΩ A BL BR CC κ, PP A BL BR CC κ ε p
          * |mgSum (pX A BL BR CC κ ε cLo') κ p|) ^ 2
        ≤ ((∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
          + (κ : ℝ) * ε + (cB + ε + cLo') * Nb) ^ 2 :=
      pow_le_pow_left₀ hm0 hred 2
    have h3 : ((κ : ℝ) * cLo' ^ 2) ^ 3
        ≤ ((∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
          + (κ : ℝ) * ε + (cB + ε + cLo') * Nb) ^ 2
          * (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
            + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2)) :=
      le_trans hanti (mul_le_mul_of_nonneg_right h2 hCpos.le)
    have h4 : ((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
          + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2))
        ≤ ((∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
          + (κ : ℝ) * ε + (cB + ε + cLo') * Nb) ^ 2 :=
      (div_le_iff₀ hCpos).mpr h3
    have hEκ : 0 ≤ (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
        * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
        + (κ : ℝ) * ε + (cB + ε + cLo') * Nb := by
      have h5 : (0 : ℝ) ≤ (κ : ℝ) * ε := by positivity
      have h6 : (0 : ℝ) ≤ (cB + ε + cLo') * Nb := mul_nonneg hc0 hNb0
      linarith
    have h5 : Real.sqrt (((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
          + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2)))
        ≤ (∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
            * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω|)
          + (κ : ℝ) * ε + (cB + ε + cLo') * Nb := by
      refine le_trans (Real.sqrt_le_sqrt h4) (le_of_eq ?_)
      exact Real.sqrt_sq hEκ
    linarith

end KServer

open KServer Race in
theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cB T pe : ℝ} {mL : ℕ}
    (A BL BR CC : ChunkSystemB X s t 0 cB T pe mL)
    (κ : ℕ) (ε : ℝ) (hε : 0 < ε) (hcB : 0 ≤ cB)
    {cLo' : ℝ} (hεLo : ε ≤ cLo') (hLocB : cLo' ≤ cB + ε)
    {Nb : ℝ} (hNb : ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
      * Nbad A BL BR CC κ cLo' ω ≤ Nb) :
    Real.sqrt (((κ : ℝ) * cLo' ^ 2) ^ 3
        / (8 * ((κ : ℝ) * (cB + ε) ^ 2) ^ 2
          + 3 * (cB + ε) ^ 2 * ((κ : ℝ) * (cB + ε) ^ 2)))
      - (κ : ℝ) * ε - (cB + ε + cLo') * Nb
      ≤ ∑ ω : RΩ A BL BR CC κ, RP A BL BR CC κ ε ω
          * |sumL A BL BR CC κ ω - sumR A BL BR CC κ ω| :=
  KServer.race_gain_bound2 A BL BR CC κ ε hε hcB hεLo hLocB hNb
