-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialNested.binary_response_spearmanSq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:39:15.111519+00:00
-- url     : https://prove2.me/submissions/363a3518-81f0-49cf-98a2-cd668d525a5c

-- Sol generated from Novelty/ZeroFitDialNested.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialNested
import Definitions.Def_Novelty_ZeroFitDialU64
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_cube_sub_self_pos
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_spearmanSq_eq

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
theorem solution(j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    spearmanSq [j, k] = 3 * (j : ℚ) * (k : ℚ) / (((j : ℚ) + k) ^ 2 - 1) := by
  have hsum : ([j, k] : List ℕ).sum = j + k := by simp
  have h2 : 2 ≤ ([j, k] : List ℕ).sum := by rw [hsum]; omega
  have hj1 : (1 : ℚ) ≤ (j : ℚ) := by exact_mod_cast hj
  have hk1 : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hcast : ((([j, k] : List ℕ).sum : ℕ) : ℚ) = (j : ℚ) + k := by rw [hsum]; push_cast; ring
  rw [spearmanSq_eq _ h2, hcast]
  have htc : tieCorr ([j, k] : List ℕ) = ((j : ℚ) ^ 3 - j) / 12 + ((k : ℚ) ^ 3 - k) / 12 := by
    simp [tieCorr]
  rw [htc]
  have h2q : (2 : ℚ) ≤ (j : ℚ) + k := by linarith
  have hne1 : ((j : ℚ) + k) ^ 2 - 1 ≠ 0 := by
    have : (4 : ℚ) ≤ ((j : ℚ) + k) ^ 2 := by nlinarith
    exact ne_of_gt (by linarith)
  have hne2 : ((j : ℚ) + k) ^ 3 - ((j : ℚ) + k) ≠ 0 := ne_of_gt (cube_sub_self_pos h2q)
  field_simp
  ring
