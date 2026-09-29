-- Prove2me | Definitions.Def_Erdos249257_TotientKernelConditional
-- name    : Erdos249257_TotientKernelConditional
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T13:48:03.452255+00:00
-- url     : https://prove2.me/theorems/f5bb7592-ddd8-4198-9396-3b45b272172d
-- title:
--   All-base totient sections and conditional rank setup
-- statement:
--   Defines base-k totient section sequences, their reduction scalar, and the canonical and complete families. Its rank result assumes independence of the canonical family.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/TotientKernelConditional.lean#L25-L35
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/TotientKernelConditional.lean#L81-L100
--   Supporting source declaration: https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/TotientKernelConditional.lean#L203-L220

import Definitions.Def_Erdos249257_TotientKernelIndex
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Totient
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Conditional exact rank for the all-base totient kernel

This module separates the two layers of the expected all-base theorem.

* The arithmetic layer is unconditional: a composite-base residue divisible
  by `k` reduces to the corresponding lower-level section by an explicit
  nonzero rational scalar.  Iterating this relation proves that the
  filtration-compatible family indexed by `TotientKernelIndex k e` spans the
  complete kernel through level `e`.
* The exact-rank conclusion is conditional on linear independence of that
  canonical family.  That hypothesis is precisely the external mathematical
  input; no theorem of Martin is formalised or assumed as an axiom here.
-/

namespace Erdos249257

open Module

/-- The `(j,r)` base-`k` kernel channel of Euler's totient, viewed over `ℚ`. -/
def allBaseTotientKernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (k ^ j * n + r)
























end Erdos249257


