-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapKernelBridge_original_five_dimensional_map_bijective
-- name    : ZetaNine.CoefficientMapKernelBridge.original_five_dimensional_map_bijective
-- status  : Open
-- author  : @Yuxuan Xu
-- created : 2026-10-04T10:48:58.17684+00:00
-- url     : https://prove2.me/theorems/ce238b53-8b97-42f6-ac2e-191364bf4a42
-- title:
--   The actual five-dimensional rational coefficient map is bijective
-- statement:
--   For each even n>=2 the original five-dimensional rational aggregate map on quartic coordinates is bijective. Injectivity follows from the actual quartic kernel result, then finite dimensionality gives surjectivity. No determinant, rank, bijection or inverse assumption is added.
-- source:
--   Zeta(9) actual original five-dimensional coefficient map kernel and rational inverse: missions/zeta9/research/coefficient-map-kernel-2026-10-04.md. Frozen source SHA256 1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb. The actual kernel, polynomial relation, bijection, inverse and sum are derived from genuine data and source proofs. Original declaration lines 232–235.

import Definitions.Def_ZetaNine_CoefficientMapKernelBridge

set_option autoImplicit false
open scoped BigOperators Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate

theorem ZetaNine.CoefficientMapKernelBridge.original_five_dimensional_map_bijective (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    Function.Bijective (quarticAggregateLinearMap n):= by sorry
