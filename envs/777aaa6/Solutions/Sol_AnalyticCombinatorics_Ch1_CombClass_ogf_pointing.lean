-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.ogf_pointing
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:39.870726+00:00
-- url     : https://prove2.me/submissions/1f841453-c6d6-4de4-8926-6d28f3c198bd

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Pointing
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.PowerSeries.Derivative

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

@[simp] lemma coeff_ogfSeq (a : ℕ → ℕ) (n : ℕ) : coeff n (ogfSeq a) = (a n : ℚ) := by
  rw [ogfSeq, coeff_mk]

attribute [instance] CombClass.finObj

@[simp] lemma CombClass.coeff_ogf (C : CombClass) (n : ℕ) :
    coeff n C.ogf = (C.counts n : ℚ) := by
  rw [CombClass.ogf, coeff_ogfSeq]

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.6 — The pointing construction Θ

Flajolet & Sedgewick, Part A, Chapter I. The *pointing* of a class `C`,
`Θ(C)`, distinguishes one of the `n` atoms of a size-`n` object: a pointed object
is a `C`-object together with a choice of one of its `n` atoms. Hence
`Θ(C)ₙ = n·Cₙ`, and the OGF is

  **`Θ(C)(z) = z·C'(z)`**

(the operator `z d/dz`). We model the pointed objects by `C.Obj n × Fin n`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma CombClass.counts_pointing (C : CombClass) (n : ℕ) :
    C.pointing.counts n = C.counts n * n := by
  change Fintype.card (C.Obj n × Fin n) = _
  rw [Fintype.card_prod, Fintype.card_fin]
  rfl

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
theorem solution (C : CombClass) :
    C.pointing.ogf = X * PowerSeries.derivativeFun C.ogf := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_pointing]
  cases n with
  | zero => simp
  | succ m =>
    rw [coeff_succ_X_mul, PowerSeries.coeff_derivativeFun, CombClass.coeff_ogf]
    push_cast
    ring
