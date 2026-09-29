-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialEffectiveBase.effBase_pooled_bracket
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:32:08.476657+00:00
-- url     : https://prove2.me/submissions/8cef1323-1452-441e-8a69-b05abbf13f31

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








/-! ## 3. Self-duality of the ceiling law -/





open Catalog.Novelty.ZeroFitDialEffectiveBase in
theorem solution:
    6.9 < effBase ((0.608 : ℝ) ^ 2) ∧ effBase ((0.608 : ℝ) ^ 2) < 7.05 := by
  set r : ℝ := (0.608 : ℝ) ^ 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; norm_num
  have hr1 : r < 1 := by rw [hrdef]; norm_num
  set s : ℝ := Real.sqrt (3 * (1 - r) * (3 + r)) with hsdef
  have hlow : 2.52 < s := by
    rw [hsdef, Real.lt_sqrt (by norm_num)]
    rw [hrdef]; norm_num
  have hhigh : s < 2.53 := by
    rw [hsdef, Real.sqrt_lt' (by norm_num)]
    rw [hrdef]; norm_num
  have hpos : (0 : ℝ) < 2 * r := by linarith
  constructor
  · rw [effBase, ← hsdef, lt_div_iff₀ hpos, hrdef]
    nlinarith [hlow]
  · rw [effBase, ← hsdef, div_lt_iff₀ hpos, hrdef]
    nlinarith [hhigh]
