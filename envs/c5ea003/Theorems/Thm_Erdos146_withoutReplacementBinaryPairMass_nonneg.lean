-- Prove2me | Theorems.Thm_Erdos146_withoutReplacementBinaryPairMass_nonneg
-- name    : Erdos146.withoutReplacementBinaryPairMass_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:41:35.817293+00:00
-- url     : https://prove2.me/theorems/9519fdc2-eec1-4470-8a30-3f16ac45770c
-- title:
--   The without-replacement pair mass is nonnegative
-- statement:
--   The joint mass arising from sampling an ordered pair of distinct indices without replacement is nonnegative (Lemma 5.2).
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L10456-L10510

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.withoutReplacementBinaryPairMass_nonneg
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (left right : Bool) :
    0 ≤ withoutReplacementBinaryPairMass parentCount oneCount left right := by sorry
