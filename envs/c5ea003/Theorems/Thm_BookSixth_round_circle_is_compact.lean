-- Prove2me | Theorems.Thm_BookSixth_round_circle_is_compact
-- name    : BookSixth.round_circle_is_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-26T19:13:49.916985+00:00
-- url     : https://prove2.me/theorems/447ecc36-9c38-481b-a4f5-9bc76f5c54a6
-- title:
--   A round circle in R^3 is a compact set
-- statement:
--   If `C` is a round circle, then `C` is a compact subset of `R^3`. By the definition of `RoundCircle`, `C` is the range of the continuous map `t |-> c + (r*cos t) * u + (r*sin t) * v` on all of `R`. The range over all of `R` equals the image of the closed interval `[0, 2*pi]`, because the map is `2*pi`-periodic, and the image of a compact set under a continuous map is compact. This is the topological input every localisation argument about a family of disjoint round circles needs: disjoint compact sets admit disjoint open neighbourhoods.
-- source:
--   Needed for BookSixth.perfect_circles_pairwise_unlinked_motion (theorem id f6a7245e-187d-4a69-8b49-100cf7e4a1cc), the only open leaf of BookSixth.sixthEditionExtension. That leaf needs disjoint open neighbourhoods of the pairwise disjoint components in order to localise an ambient isotopy near each circle, and `IsCompact.disjoint_nhdsSet_left` (Mathlib/Topology/Compactness/Compact.lean:250) turns `IsCompact` into such neighbourhoods. The definition `RoundCircle` gives `C = Set.range g` for a continuous `g : R -> Space3`, whose range is the image of the compact interval `[0, 2*pi]` because `g` is `2*pi`-periodic via `Real.cos_add_two_pi` and `Real.sin_add_two_pi`.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_is_compact {C : Set Space3} (hC : RoundCircle C) : IsCompact C := by sorry
