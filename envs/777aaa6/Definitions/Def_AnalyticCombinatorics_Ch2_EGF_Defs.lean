-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch2_EGF_Defs
-- name    : AnalyticCombinatorics_Ch2_EGF_Defs
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-25T09:32:58.686972+00:00
-- url     : https://prove2.me/theorems/cbe4e34d-1cad-4603-b50e-d0e6f330b5b8
-- title:
--   Finite graded classes and exponential generating functions
-- statement:
--   For a class with finitely many size-n objects, its exponential generating function has rational coefficient equal to the size-n count divided by n!. The concrete classes include permutations of n labels and one object in every size. The formal exponential uses the same factorial normalization.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch2/EGF/Defs.lean Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
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
# Ch2 §II.1 — Labelled structures and exponential generating functions

Flajolet & Sedgewick, Part A, Chapter II. A *labelled* class is again a graded
family of finite types (we reuse `CombClass`), but is enumerated by its
*exponential* generating function (EGF)

  `A(z) = ∑ₙ Aₙ zⁿ/n!`.

This file defines the EGF and two foundational flagships:
- permutations (`Perm (Fin n)`, `Aₙ = n!`) with EGF `1/(1 - z)`;
- the "set" class (one object of each size) with EGF `e^z`.

The labelled product (the defining feature of EGFs) is developed separately.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The exponential generating function of a counting sequence `a : ℕ → ℕ`:
`A(z) = ∑ₙ aₙ zⁿ/n!`, a formal power series over `ℚ` (F&S §II.1). -/
noncomputable def egfSeq (a : ℕ → ℕ) : ℚ⟦X⟧ := mk fun n => (a n : ℚ) / (n.factorial : ℚ)

/-- The exponential generating function of a (labelled) combinatorial class. -/
noncomputable def CombClass.egf (C : CombClass) : ℚ⟦X⟧ := egfSeq C.counts

/-! ### Permutations -/

/-- The class of permutations (F&S §II.1): a size-`n` object is a permutation of
its `n` labels. -/
def CombClass.permutations : CombClass where
  Obj n := Equiv.Perm (Fin n)
  finObj _ := inferInstance

/-! ### The set class -/

/-- The "set" class (F&S §II.1): one object of each size — the labelled atom of the
`SET` construction. -/
def CombClass.setClass : CombClass where
  Obj _ := Unit
  finObj _ := inferInstance

end AnalyticCombinatorics.Ch1


