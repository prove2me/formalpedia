-- Prove2me | Theorems.Thm_Catalog_Novelty_ZeroFitDialEffectiveBase_nested_ge_one_sided
-- name    : Catalog.Novelty.ZeroFitDialEffectiveBase.nested_ge_one_sided
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:18:26.136327+00:00
-- url     : https://prove2.me/theorems/af819035-4bb5-4f73-9529-624afac50558
-- title:
--   Response-granularity monotonicity.
-- statement:
--   **Response-granularity monotonicity.**  In the nested (two-sided) model, coarsening
--   the response strictly *raises* the attainable coefficient: the nested ceiling always
--   dominates the one-sided ceiling of the coarse profile.
--
--   ```lean
--   theorem Catalog.Novelty.ZeroFitDialEffectiveBase.nested_ge_one_sided(L : List (List ℕ)) (h : 2 ≤ L.flatten.sum) :
--       spearmanSq (L.map List.sum) ≤ nestedSpearmanSq L := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ZeroFitDialEffectiveBase.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ZeroFitDialEffectiveBase.lean#L46

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

theorem Catalog.Novelty.ZeroFitDialEffectiveBase.nested_ge_one_sided(L : List (List ℕ)) (h : 2 ≤ L.flatten.sum) :
    spearmanSq (L.map List.sum) ≤ nestedSpearmanSq L := by sorry
