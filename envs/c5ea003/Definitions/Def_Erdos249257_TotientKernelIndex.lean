-- Prove2me | Definitions.Def_Erdos249257_TotientKernelIndex
-- name    : Erdos249257_TotientKernelIndex
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T13:45:56.716651+00:00
-- url     : https://prove2.me/theorems/0f02d60f-79a9-4088-ac9c-53fccdc393db
-- title:
--   Finite indices for all-base totient sections
-- statement:
--   Defines the two distinguished zero-residue channels and the nonzero residue indices through a finite level. For base $k ≥ 2$, their count is $k^e + 1$; this module does not establish linear independence.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/TotientKernelIndex.lean#L46-L55
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/TotientKernelIndex.lean#L264-L285

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite indices for the all-base totient kernel

This module records the combinatorial part of the expected finite-level
all-base totient-kernel basis.  There are two distinguished zero-residue
indices, followed at level `j + 1` by residues written uniquely in the form

`k * q + (d + 1)`, with `q < k^j` and `d < k - 1`.

For `k ≥ 2`, these coordinates give positive residues below `k^(j+1)` that
are not divisible by `k`.  Their finite cardinality is

`2 + ∑ j in range e, k^j * (k - 1) = k^e + 1`.

This is only the index and cardinality layer.  It does not assert linear
independence of the corresponding totient sections; that theorem remains an
external mathematical input in the all-base argument.
-/

namespace Erdos249257

/-- The two distinguished zero-residue channels, conventionally denoted
`F00` and `F10`. -/
inductive TotientKernelHeadIndex
  | F00
  | F10
  deriving DecidableEq

instance : Fintype TotientKernelHeadIndex where
  elems := {.F00, .F10}
  complete := by
    intro i
    cases i <;> simp

























/-! ## Exact fixed-level residue coordinates -/























end Erdos249257


