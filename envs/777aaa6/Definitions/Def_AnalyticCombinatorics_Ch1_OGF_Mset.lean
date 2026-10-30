-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Mset
-- name    : AnalyticCombinatorics_Ch1_OGF_Mset
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:06:48.385125+00:00
-- url     : https://prove2.me/theorems/89b121d8-3347-4b80-bbd4-916bec08ad45
-- title:
--   Partition-decorated multisets grouped by positive size
-- statement:
--   A size-n object is a partition λ of n and, at every size m≤n, a multiset of size r_m(λ) from C_m. All parts of λ are positive, so r_0=0 and zero-size C-objects are ignored. Rational coefficients are discrete and formal power-series limits are coefficientwise. The unrestricted multiset interpretation needs C_0 empty.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Mset.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.2 — The multiset construction MSET(C): counts layer

Flajolet & Sedgewick, Part A, Chapter I, §I.2. `MSET(C)` forms finite multisets of
C-objects (`C₀=∅`). Grouping a multiset by object size, a size-`n` object is a
partition `p` of `n` (recording the multiplicities of each size) together with, for
each size `m`, a size-`(mult m)` multiset of the `Cₘ` objects of that size (a `Sym`).

This file builds the graded `Fintype` model and the counting identity, and connects
it to Mathlib's `Nat.Partition.genFun`:

  `MSET(C)ₙ = ∑_{p:Partition n} ∏_m multichoose(Cₘ, mult_m p)
            = genFun (fun m j => multichoose(Cₘ, j)) |>.coeff n`.

The Euler product OGF `∏_m (1 - z^m)^{-Cₘ}` is proved in the OGF layer. (For `C = ℙ`,
`multichoose 1 k = 1`, recovering the partition flagship.)
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The multiset construction `MSET(C)` (F&S §I.2), modelled by grouping a multiset
of C-objects by size: a partition `p` of `n` together with, for each size `m`, a
size-`(p.parts.count m)` multiset (`Sym`) of the size-`m` objects of `C`. Faithful
when `C₀=∅`. -/
noncomputable def CombClass.mset (C : CombClass) : CombClass where
  Obj n := Σ p : Nat.Partition n, ∀ m : Fin (n + 1), Sym (C.Obj m.val) (p.parts.count m.val)
  finObj _ := by classical infer_instance

section EulerProduct

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

local instance instTopRatMset : TopologicalSpace ℚ := ⊥

end EulerProduct

end AnalyticCombinatorics.Ch1


