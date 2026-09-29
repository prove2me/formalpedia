-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialNested.nested_spearmanSq_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:41:04.831981+00:00
-- url     : https://prove2.me/submissions/b84fe768-8d9b-4461-91fd-3bc77b60f8c8

-- Sol generated from Novelty/ZeroFitDialNested.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialNested
import Definitions.Def_Novelty_ZeroFitDialU64
import Theorems.Thm_Catalog_Novelty_ZeroFitDialNested_flatten_sum
import Theorems.Thm_Catalog_Novelty_ZeroFitDialNested_tieCorr_flatten_le
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_ssR_nonneg
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_ssS_eq_ssR_add
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_ssS_total

/-!
# Nested tie profiles: the zero-fit dial when *both* sides are tied

Cycle 2 of the round-61 investigation.  `Novelty.ZeroFitDialU64` established the
tie-attenuation law for a tied statistic `T` measured against a tie-*refining*
response, and showed that at bitlen 64 the 2-adic tie ceiling
(`≈ 0.9258`) is far above the recorded dial (`0.648`), so tie granularity of the
zero-count statistic cannot explain the observed decline of the dial.

The natural next suspect is granularity of the **response**.  Here we prove the
two-sided law for *nested* profiles: if one variable's tie blocks refine the
other's, then

`ρ² = (V - T_coarse) / (V - T_fine)`,  where `V = (n³-n)/12`

and `T_•` are the Kendall tie corrections of the two profiles.  The one-sided law
is the special case `T_fine = 0`.

## Main results

* `spNest_eq_ssR_coarse` — the midrank collapse identity survives nesting:
  the centred cross-product of the two midrank vectors equals the *coarse*
  between-block sum of squares.
* `nested_spearmanSq_eq` — the two-sided attenuation law.
* `tieCorr_flatten_le` — refinement decreases the tie correction (superadditivity
  of `m ↦ m³ - m`), hence `nested_spearmanSq_le_one`.
* `nested_of_fine_tiefree` — the one-sided law is recovered.
* `binary_response_spearmanSq` — **exact** ceiling for a binary response with
  `j` positives and `k` negatives against a tie-free statistic:
  `ρ² = 3jk/((j+k)² - 1)`, i.e. asymptotically `ρ = √(3q(1-q))`.
* `balanced_binary_ceiling` — the balanced binary ceiling `ρ² = 3j²/(4j²-1) > 3/4`
  (`ρ → √3/2 ≈ 0.8660`).
* `u64_binary_calibration` — the recorded pooled reading `0.648` is reproduced to
  `10⁻⁴` by a binary response with base rate `16.83 %`; combined with
  `u64_binary_rate_forced`, any binary response with base rate above `25 %` is
  *excluded* by the measurement.

The scientific content is a falsifiable prediction: under the response-granularity
explanation of the dial's decline, the bitlen-64 rate variable must be
(effectively) a two-class variable with minority mass near `17 %`, and the dial can
never exceed `√3/2` regardless of bitlen.
-/

open Finset

open Catalog.Novelty.ZeroFitDialNested

open Catalog.Novelty.ZeroFitDialU64

/-! ## 1. Weighted midranks inside a coarse block -/





/-! ## 2. Nested profiles -/







/-! ## 3. Refinement decreases ties -/






/-! ## 4. Binary responses: the exact `√(3q(1-q))` ceiling -/




/-! ## 5. Calibrating the recorded U64 reading against a binary response -/




open Catalog.Novelty.ZeroFitDialNested in
theorem solution(L : List (List ℕ)) (h : 2 ≤ L.flatten.sum) :
    0 ≤ nestedSpearmanSq L ∧ nestedSpearmanSq L ≤ 1 := by
  have hn : (2 : ℚ) ≤ (L.flatten.sum : ℚ) := by exact_mod_cast h
  set V : ℚ := ((L.flatten.sum : ℚ) ^ 3 - L.flatten.sum) / 12 with hVdef
  have hsum : (L.map List.sum).sum = L.flatten.sum := (flatten_sum L).symm
  have hcoarseS : ssS (gmean L.flatten) (L.map List.sum) 0 = V := by
    have hg : gmean (L.map List.sum) = gmean L.flatten := by rw [gmean, gmean, hsum]
    rw [← hg, ssS_total, hsum]
  have hA : ssR (gmean L.flatten) (L.map List.sum) 0 = V - tieCorr (L.map List.sum) := by
    have := ssS_eq_ssR_add (gmean L.flatten) (L.map List.sum) 0
    rw [hcoarseS] at this; linarith
  have hB : ssR (gmean L.flatten) L.flatten 0 = V - tieCorr L.flatten := by
    have := ssS_eq_ssR_add (gmean L.flatten) L.flatten 0
    rw [ssS_total L.flatten] at this; linarith
  have hAB : ssR (gmean L.flatten) (L.map List.sum) 0 ≤ ssR (gmean L.flatten) L.flatten 0 := by
    rw [hA, hB]
    have := tieCorr_flatten_le L
    linarith
  have hA0 : 0 ≤ ssR (gmean L.flatten) (L.map List.sum) 0 := ssR_nonneg _ _ _
  have hB0 : 0 ≤ ssR (gmean L.flatten) L.flatten 0 := ssR_nonneg _ _ _
  rcases eq_or_lt_of_le hB0 with hzero | hpos
  · rw [nestedSpearmanSq, ← hzero, div_zero]
    exact ⟨le_refl 0, by norm_num⟩
  · exact ⟨div_nonneg hA0 (le_of_lt hpos), by rw [nestedSpearmanSq, div_le_one hpos]; exact hAB⟩
