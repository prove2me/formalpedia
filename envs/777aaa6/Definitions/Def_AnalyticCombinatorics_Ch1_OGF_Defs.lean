-- Prove2me | Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Defs
-- name    : AnalyticCombinatorics_Ch1_OGF_Defs
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-24T21:21:12.528991+00:00
-- url     : https://prove2.me/theorems/be0b7904-14ac-4a13-ac70-1f8d143c3e74
-- title:
--   Finite combinatorial classes and ordinary generating functions
-- statement:
--   A combinatorial class is a family of finite sets of objects, one set for each natural-number size. If $a_n$ is the number of objects of size $n$, its ordinary generating function over the rational numbers is
--
--   $$A(X)=\sum_{n\geq0}a_nX^n\in\mathbb{Q}[[X]].$$
--
--   This foundation provides the class, its counting sequence and its formal generating function, together with the empty class, the class with one size-zero object and the class with one size-one object. These objects give a common representation for the later ordered-sequence constructions; no analytic convergence assertion is part of their definition.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/OGF/Defs.lean. Definitions for the sequence-construction portion of Flajolet and Sedgewick, Analytic Combinatorics (Cambridge University Press, 2009), Chapter I. Source code license: Apache-2.0; immutable license text: https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE.

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Ch1 §I.1 — Combinatorial classes and ordinary generating functions

A faithful encoding of Flajolet & Sedgewick, *Analytic Combinatorics*, Part A,
Chapter I, §I.1. A combinatorial class is a set of objects equipped with a size
function such that only finitely many objects have any given size. We encode it
as a graded family of finite types `Obj : ℕ → Type`, where `Obj n` is the set of
objects of size `n`. Its counting sequence is `Aₙ = #(Obj n)`, and its *ordinary
generating function* (OGF) is `A(z) = ∑ₙ Aₙ zⁿ`, here a formal power series over
`ℚ`.

This file defines the OGF, the `CombClass` structure, and the three primitive
classes (empty `∅`, neutral `ε`, atom `Z`) with their counting sequences and
generating functions `ε(z) = 1`, `Z(z) = z`. The admissible constructions (sum,
product, sequence) and their transfer theorems live in sibling files.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The ordinary generating function of a counting sequence `a : ℕ → ℕ`, as a
formal power series over `ℚ` (F&S §I.1: `A(z) = ∑ₙ aₙ zⁿ`). The class-level
OGF `CombClass.ogf` is defined on top of this. -/
noncomputable def ogfSeq (a : ℕ → ℕ) : ℚ⟦X⟧ := mk fun n => (a n : ℚ)

/-- A combinatorial class (F&S §I.1): a graded family of finite types, with
`Obj n` the objects of size `n`. The `Fintype` field records that each size
class is finite, which is exactly F&S's standing finiteness condition. -/
structure CombClass where
  /-- Objects of size `n`. -/
  Obj : ℕ → Type
  /-- Each size class is finite. -/
  finObj : ∀ n, Fintype (Obj n)

attribute [instance] CombClass.finObj

/-- The counting sequence `Aₙ = #{objects of size n}`. -/
def CombClass.counts (C : CombClass) (n : ℕ) : ℕ := Fintype.card (C.Obj n)

/-- The ordinary generating function of a combinatorial class. -/
noncomputable def CombClass.ogf (C : CombClass) : ℚ⟦X⟧ := ogfSeq C.counts

/-! ### Primitive classes

We encode the primitive classes with `Obj n := Fin (· n)` so that the `Fintype`
instance is uniform; their entire content is their counting sequence. -/

/-- The empty class `∅`: no objects of any size. -/
def CombClass.empty : CombClass where
  Obj _ := Fin 0
  finObj _ := inferInstance

/-- The neutral class `ε`: a single object of size `0`. -/
def CombClass.neutral : CombClass where
  Obj n := Fin (if n = 0 then 1 else 0)
  finObj _ := inferInstance

/-- The atomic class `Z`: a single object of size `1`. -/
def CombClass.atom : CombClass where
  Obj n := Fin (if n = 1 then 1 else 0)
  finObj _ := inferInstance

end AnalyticCombinatorics.Ch1


