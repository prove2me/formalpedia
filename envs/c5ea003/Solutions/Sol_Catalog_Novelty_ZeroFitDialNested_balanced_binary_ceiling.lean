-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialNested.balanced_binary_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:41:03.534986+00:00
-- url     : https://prove2.me/submissions/73df3b1d-a147-4dfd-9c34-09d65e118f7f

-- Sol generated from Novelty/ZeroFitDialNested.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialNested
import Definitions.Def_Novelty_ZeroFitDialU64
import Theorems.Thm_Catalog_Novelty_ZeroFitDialNested_binary_response_spearmanSq

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
theorem solution(j : ℕ) (hj : 1 ≤ j) :
    spearmanSq [j, j] = 3 * (j : ℚ) ^ 2 / (4 * (j : ℚ) ^ 2 - 1) ∧
      3 / 4 < spearmanSq [j, j] := by
  have hj1 : (1 : ℚ) ≤ (j : ℚ) := by exact_mod_cast hj
  have hform : spearmanSq [j, j] = 3 * (j : ℚ) ^ 2 / (4 * (j : ℚ) ^ 2 - 1) := by
    rw [binary_response_spearmanSq j j hj hj]
    have hne : ((j : ℚ) + j) ^ 2 - 1 ≠ 0 := by nlinarith
    have hne' : 4 * (j : ℚ) ^ 2 - 1 ≠ 0 := by nlinarith
    field_simp
    ring
  refine ⟨hform, ?_⟩
  rw [hform]
  rw [lt_div_iff₀ (by nlinarith)]
  nlinarith
