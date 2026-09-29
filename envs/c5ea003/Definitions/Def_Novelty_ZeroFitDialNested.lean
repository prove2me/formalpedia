-- Prove2me | Definitions.Def_Novelty_ZeroFitDialNested
-- name    : Novelty_ZeroFitDialNested
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:55:14.758162+00:00
-- url     : https://prove2.me/theorems/d36d0ae4-6773-4664-a1d5-6e2056686fe3
-- title:
--   Aether Catalog definitions — Novelty_ZeroFitDialNested
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ZeroFitDialNested`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ZeroFitDialNested.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialU64

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

namespace Catalog.Novelty.ZeroFitDialNested

open Catalog.Novelty.ZeroFitDialU64

/-! ## 1. Weighted midranks inside a coarse block -/

/-- Sum of the fine midranks weighted by the fine block sizes, starting at offset `c`. -/
def wsum : List ℕ → ℚ → ℚ
  | [], _ => 0
  | p :: P, c => (p : ℚ) * (c + ((p : ℚ) + 1) / 2) + wsum P (c + p)


/-- Centred cross-product contributed by one coarse block with midrank `R`. -/
def spBlock (mu R : ℚ) : List ℕ → ℚ → ℚ
  | [], _ => 0
  | p :: P, c => (p : ℚ) * (R - mu) * ((c + ((p : ℚ) + 1) / 2) - mu) + spBlock mu R P (c + p)


/-! ## 2. Nested profiles -/

/-- Centred cross-product of the coarse midranks against the fine midranks. -/
def spNest (mu : ℚ) : List (List ℕ) → ℚ → ℚ
  | [], _ => 0
  | P :: L, c => spBlock mu (c + ((P.sum : ℚ) + 1) / 2) P c + spNest mu L (c + P.sum)




/-- Squared Spearman coefficient of a nested pair of tie profiles: coarse variable against fine
variable, both scored by midranks. -/
def nestedSpearmanSq (L : List (List ℕ)) : ℚ :=
  ssR (gmean L.flatten) (L.map List.sum) 0 / ssR (gmean L.flatten) L.flatten 0


/-! ## 3. Refinement decreases ties -/






/-! ## 4. Binary responses: the exact `√(3q(1-q))` ceiling -/




/-! ## 5. Calibrating the recorded U64 reading against a binary response -/



end Catalog.Novelty.ZeroFitDialNested


