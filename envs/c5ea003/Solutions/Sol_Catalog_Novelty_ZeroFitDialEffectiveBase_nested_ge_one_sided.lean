-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialEffectiveBase.nested_ge_one_sided
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:39:13.967224+00:00
-- url     : https://prove2.me/submissions/1532def4-73ea-47ec-9948-acc842fb2c5a

-- Sol generated from Novelty/ZeroFitDialEffectiveBase.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialEffectiveBase
import Definitions.Def_Novelty_ZeroFitDialNested
import Definitions.Def_Novelty_ZeroFitDialU64
import Definitions.Def_Novelty_ZeroFitDialU76
import Theorems.Thm_Catalog_Novelty_ZeroFitDialNested_flatten_sum
import Theorems.Thm_Catalog_Novelty_ZeroFitDialNested_nested_spearmanSq_eq
import Theorems.Thm_Catalog_Novelty_ZeroFitDialNested_tieCorr_flatten_le
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_cube_sub_self_pos
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_spearmanSq_eq
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_ssR_nonneg
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_ssS_eq_ssR_add
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_ssS_total
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_sub_div_twelve
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_tieCorr_nonneg

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
theorem solution(L : List (List ℕ)) (h : 2 ≤ L.flatten.sum) :
    spearmanSq (L.map List.sum) ≤ nestedSpearmanSq L := by
  have hn : (2 : ℚ) ≤ (L.flatten.sum : ℚ) := by exact_mod_cast h
  have hsum : (L.map List.sum).sum = L.flatten.sum := (flatten_sum L).symm
  have h2 : 2 ≤ (L.map List.sum).sum := by rw [hsum]; exact h
  have hV : (0 : ℚ) < ((L.flatten.sum : ℚ) ^ 3 - L.flatten.sum) := cube_sub_self_pos hn
  set V : ℚ := ((L.flatten.sum : ℚ) ^ 3 - L.flatten.sum) / 12 with hVdef
  have hVpos : 0 < V := by rw [hVdef]; linarith
  -- the one-sided coefficient of the coarse profile is `(V - T_coarse)/V`
  have hone : spearmanSq (L.map List.sum) = (V - tieCorr (L.map List.sum)) / V := by
    rw [spearmanSq_eq _ h2, hsum, hVdef]
    rw [sub_div_twelve _ _ (ne_of_gt hV)]
  have hnest : nestedSpearmanSq L = (V - tieCorr (L.map List.sum)) / (V - tieCorr L.flatten) := by
    rw [nested_spearmanSq_eq L, hVdef]
  -- numerator is nonnegative, and the nested denominator is at most `V`
  have hA0 : 0 ≤ V - tieCorr (L.map List.sum) := by
    have hR : ssR (gmean L.flatten) (L.map List.sum) 0 = V - tieCorr (L.map List.sum) := by
      have hg : gmean (L.map List.sum) = gmean L.flatten := by rw [gmean, gmean, hsum]
      have hS : ssS (gmean L.flatten) (L.map List.sum) 0 = V := by
        rw [← hg, ssS_total, hsum, hVdef]
      have := ssS_eq_ssR_add (gmean L.flatten) (L.map List.sum) 0
      rw [hS] at this; linarith
    rw [← hR]; exact ssR_nonneg _ _ _
  have hfine : tieCorr L.flatten ≤ tieCorr (L.map List.sum) := tieCorr_flatten_le L
  have hfine0 : 0 ≤ tieCorr L.flatten := tieCorr_nonneg _
  rw [hone, hnest]
  rcases eq_or_lt_of_le (by linarith : (0 : ℚ) ≤ V - tieCorr L.flatten) with hB | hB
  · -- degenerate case: both coefficients vanish
    have hAzero : V - tieCorr (L.map List.sum) = 0 := by linarith
    rw [hAzero, ← hB]
    simp
  · exact div_le_div_of_nonneg_left hA0 hB (by linarith)
