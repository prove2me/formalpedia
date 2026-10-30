-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Pset
-- name    : AnalyticCombinatorics_Ch1_OGF_Pset
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:06:41.603052+00:00
-- url     : https://prove2.me/theorems/cf91e39d-fc49-492f-af6a-b0d04b690ef2
-- title:
--   Partition-decorated finite subsets grouped by positive size
-- statement:
--   A size-n object is a partition λ of n and, at every size m≤n, a finite subset of C_m with cardinality r_m(λ). Since partition parts are positive, no zero-size C-object can be chosen. Rational coefficients are discrete and formal limits are coefficientwise. The unrestricted finite-subset interpretation needs C_0 empty.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Pset.lean. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.2 — The powerset construction PSET(C)

Flajolet & Sedgewick, Part A, Chapter I, §I.2. `PSET(C)` forms finite *sets* of
C-objects (each object used at most once, `C₀=∅`). Grouping a set by object size, a
size-`n` object is a partition `p` of `n` together with, for each size `m`, a
*subset* of card `(mult m)` of the `Cₘ` objects of that size. The number of size-`k`
subsets of a `c`-set is `choose(c,k)`, so

  `PSET(C)ₙ = ∑_{p:Partition n} ∏_m choose(Cₘ, mult_m p)
            = genFun (fun m j => choose(Cₘ, j)) |>.coeff n`,

and the OGF is `PSET(C)(z) = ∏_{m≥1} (1 + z^m)^{Cₘ}` (since `∑_k choose(c,k) x^k =
(1+x)^c`). The construction mirrors `MSET` with subsets/`choose` in place of
multisets/`multichoose`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The powerset construction `PSET(C)` (F&S §I.2): a partition `p` of `n` together
with, for each size `m`, a card-`(p.parts.count m)` subset of the size-`m` objects of
`C`. Faithful when `C₀=∅`. -/
noncomputable def CombClass.pset (C : CombClass) : CombClass where
  Obj n := Σ p : Nat.Partition n,
    ∀ m : Fin (n + 1), { s : Finset (C.Obj m.val) // s.card = p.parts.count m.val }
  finObj _ := by classical infer_instance

section EulerProduct

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

local instance instTopRatPset : TopologicalSpace ℚ := ⊥

end EulerProduct

end AnalyticCombinatorics.Ch1


