-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialEffectiveBase.effBase_spec
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:32:15.618237+00:00
-- url     : https://prove2.me/submissions/01810db2-2ecd-4888-8469-b0dc0ab941da

-- Sol generated from Novelty/ZeroFitDialEffectiveBase.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialEffectiveBase
import Definitions.Def_Novelty_ZeroFitDialNested
import Definitions.Def_Novelty_ZeroFitDialU64
import Definitions.Def_Novelty_ZeroFitDialU76

/-!
# The effective base of the zero-fit dial, and the exclusion of response granularity

Cycle 3 of the round-65 (bitlen-76) investigation.

`Novelty.ZeroFitDialU76` proved the `p`-adic ceiling law
`ρ²(p,b) = (3p/(p²+p+1))·(1+1/(p^b(p^b+1)))` and showed that the *unique* base whose
asymptotic ceiling sits inside the observed seed window at bitlen 76 is `p = 7`.
Two questions remain open after that cycle:

1. *Could response-side granularity (a coarse `rate`) explain the observed
   attenuation instead?*  Answer: **no** — `nested_ge_one_sided` shows that in the
   nested model of `Novelty.ZeroFitDialNested` a coarser *response* can only push the
   ceiling **up**, never down.  Combined with `Novelty.ZeroFitDialTruncation`
   (truncation keeps `ρ² ≥ 3/4`) and `tie_mechanism_excluded_64_76`, every purely
   *tie-theoretic* explanation of the dial is now closed off.
2. *Is `7` an artefact of the discrete search, or is the continuous inverse of the
   ceiling law genuinely near `7`?*  Answer: the continuous inverse
   `effBase r = ((3-r) + √(3(1-r)(3+r)))/(2r)` satisfies `3·effBase r/(effBase r²+effBase r+1) = r`
   exactly (`effBase_spec`), takes the value `7` exactly at `r = 7/19`
   (`effBase_seven`), and at the recorded pooled dial `r = 0.608²` lies in
   `(6.9, 7.05)` (`effBase_pooled_bracket`).

## Main results

* `nested_ge_one_sided` — response granularity raises, never lowers, the ceiling.
* `u76_not_explained_by_response_ties` — hence no nested profile over the dyadic
  bitlen-76 coarse profile can reach the recorded dial.
* `effBase_spec`, `effBase_gt_one`, `effBase_seven`, `effBase_pooled_bracket` — the
  continuous effective base.
-/

open Finset

open Catalog.Novelty.ZeroFitDialEffectiveBase

open Catalog.Novelty.ZeroFitDialU64 Catalog.Novelty.ZeroFitDialNested
open Catalog.Novelty.ZeroFitDialU76

/-! ## 1. Response granularity can only raise the ceiling -/



/-! ## 2. The continuous effective base -/


lemma disc_nonneg {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) : 0 ≤ 3 * (1 - r) * (3 + r) := by
  have : 0 ≤ 1 - r := by linarith
  nlinarith

lemma disc_sq {r : ℝ} (h0 : 0 < r) (h1 : r ≤ 1) :
    Real.sqrt (3 * (1 - r) * (3 + r)) ^ 2 = 9 - 6 * r - 3 * r ^ 2 := by
  rw [Real.sq_sqrt (disc_nonneg h0 h1)]
  ring

/-- The effective base is at least one (and exceeds one strictly below `r = 1`). -/
theorem effBase_gt_one {r : ℝ} (h0 : 0 < r) (h1 : r < 1) : 1 < effBase r := by
  have hs : 0 ≤ Real.sqrt (3 * (1 - r) * (3 + r)) := Real.sqrt_nonneg _
  have hspos : 0 < Real.sqrt (3 * (1 - r) * (3 + r)) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  rw [effBase, lt_div_iff₀ (by linarith)]
  linarith




/-! ## 3. Self-duality of the ceiling law -/





open Catalog.Novelty.ZeroFitDialEffectiveBase in
theorem solution{r : ℝ} (h0 : 0 < r) (h1 : r < 1) :
    3 * effBase r / ((effBase r) ^ 2 + effBase r + 1) = r := by
  have hp1 : 1 < effBase r := effBase_gt_one h0 h1
  have hden : (0 : ℝ) < (effBase r) ^ 2 + effBase r + 1 := by nlinarith
  have hsq := disc_sq h0 (le_of_lt h1)
  set s : ℝ := Real.sqrt (3 * (1 - r) * (3 + r)) with hsdef
  have hp : effBase r = ((3 - r) + s) / (2 * r) := rfl
  have hquad : r * (effBase r) ^ 2 - (3 - r) * effBase r + r = 0 := by
    rw [hp]
    field_simp
    nlinarith [hsq]
  rw [eq_comm, eq_div_iff (ne_of_gt hden)]
  nlinarith [hquad]
