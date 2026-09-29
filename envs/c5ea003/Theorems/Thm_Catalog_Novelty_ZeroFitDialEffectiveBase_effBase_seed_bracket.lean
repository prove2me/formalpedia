-- Prove2me | Theorems.Thm_Catalog_Novelty_ZeroFitDialEffectiveBase_effBase_seed_bracket
-- name    : Catalog.Novelty.ZeroFitDialEffectiveBase.effBase_seed_bracket
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:17:57.423732+00:00
-- url     : https://prove2.me/theorems/811a4055-11e8-4ba2-9c79-bd5ecffbcfe0
-- title:
--   The two extreme recorded seeds put the effective base inside `(6.6, 7.4)`: the
-- statement:
--   The two extreme recorded seeds put the effective base inside `(6.6, 7.4)`: the
--   measurement pins the base to within roughly `±0.4` of `7`.
--
--   ```lean
--   theorem Catalog.Novelty.ZeroFitDialEffectiveBase.effBase_seed_bracket:
--       (6.6 < effBase ((0.593 : ℝ) ^ 2) ∧ effBase ((0.593 : ℝ) ^ 2) < 7.4) ∧
--       (6.6 < effBase ((0.618 : ℝ) ^ 2) ∧ effBase ((0.618 : ℝ) ^ 2) < 7.4) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ZeroFitDialEffectiveBase.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ZeroFitDialEffectiveBase.lean#L184

-- Thm stub generated from Novelty/ZeroFitDialEffectiveBase.lean
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

theorem Catalog.Novelty.ZeroFitDialEffectiveBase.effBase_seed_bracket:
    (6.6 < effBase ((0.593 : ℝ) ^ 2) ∧ effBase ((0.593 : ℝ) ^ 2) < 7.4) ∧
    (6.6 < effBase ((0.618 : ℝ) ^ 2) ∧ effBase ((0.618 : ℝ) ^ 2) < 7.4) := by sorry
