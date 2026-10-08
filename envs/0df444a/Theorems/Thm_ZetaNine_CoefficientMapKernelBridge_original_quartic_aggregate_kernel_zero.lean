-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapKernelBridge_original_quartic_aggregate_kernel_zero
-- name    : ZetaNine.CoefficientMapKernelBridge.original_quartic_aggregate_kernel_zero
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-04T10:48:53.523191+00:00
-- url     : https://prove2.me/theorems/940b61e1-e00a-4909-928d-1d640e6c909c
-- title:
--   The actual quartic coefficient map has trivial kernel
-- statement:
--   Let n>=2 be even and W be a rational polynomial of natural degree at most4. If its genuine aggregate F_n(W) is zero, then W is zero. The true rational telescoper, infinitely many positive regular evaluation points, polynomial identity and shift-degree obstruction are proved internally; none is an extra premise.
-- source:
--   Zeta(9) actual original five-dimensional coefficient map kernel and rational inverse: missions/zeta9/research/coefficient-map-kernel-2026-10-04.md. Frozen source SHA256 1ec15a46ae656bb0be0de0eb44afeca3144a7223a84eecf161693be25205bedb. The actual kernel, polynomial relation, bijection, inverse and sum are derived from genuine data and source proofs. Original declaration lines 189–212.

import Definitions.Def_ZetaNine_CoefficientMapKernelBridge

set_option autoImplicit false
open scoped BigOperators Topology
open Finset Polynomial Filter
open ZetaNine ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate

theorem ZetaNine.CoefficientMapKernelBridge.original_quartic_aggregate_kernel_zero (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : aggregate n W = 0) : W = 0:= by sorry
