-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_EGF_LabelledProduct
-- name    : AnalyticCombinatorics_Ch2_EGF_LabelledProduct
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:33:03.019256+00:00
-- url     : https://prove2.me/theorems/01acda61-9e47-4928-b516-bb3f91368f6b
-- title:
--   Products on disjoint labelled subsets
-- statement:
--   A size-n labelled product object chooses a subset of k labels, an object of size k from the first component class, and an object of size n−k from the second. The complement supplies the remaining labels, and all choices form finite types.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/LabelledProduct.lean Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Fintype.Powerset
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch2 §II.1 — The labelled product

Flajolet & Sedgewick, Part A, Chapter II, the labelled (partitional) product, the
defining construction of the EGF framework. To form `A ⋆ B` on `n` labels, one
chooses which `k` of the labels go to the `A`-component (a `k`-subset) and puts an
`A`-structure on them and a `B`-structure on the remaining `n-k`. Hence

  `(A ⋆ B)ₙ = ∑_{k} C(n,k) · Aₖ · B_{n-k}`   (binomial convolution),

and therefore the EGFs multiply:

  **`(A ⋆ B)(z) = A(z) · B(z)`**   (F&S Theorem II.1).
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- The labelled product `A ⋆ B` (F&S §II.1): a size-`n` object chooses a `k`-subset
`S` of the `n` labels, an `A`-structure on `S`, and a `B`-structure on the rest. -/
def CombClass.lprod (A B : CombClass) : CombClass where
  Obj n := Σ k : Fin (n + 1),
    { S : Finset (Fin n) // S.card = k } × A.Obj k × B.Obj (n - k)
  finObj _ := inferInstance

end AnalyticCombinatorics.Ch1


