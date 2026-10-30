-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.ogf_sum
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:20.627607+00:00
-- url     : https://prove2.me/submissions/f8fb31a7-7046-4db3-a4fb-a80f3597b71d

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sum
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

@[simp] lemma coeff_ogfSeq (a : ℕ → ℕ) (n : ℕ) : coeff n (ogfSeq a) = (a n : ℚ) := by
  rw [ogfSeq, coeff_mk]

attribute [instance] CombClass.finObj

@[simp] lemma CombClass.coeff_ogf (C : CombClass) (n : ℕ) :
    coeff n C.ogf = (C.counts n : ℚ) := by
  rw [CombClass.ogf, coeff_ogfSeq]

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.2 — The combinatorial sum (disjoint union) construction

Flajolet & Sedgewick, Part A, Chapter I, §I.2, first admissible construction.
If `A = B + C` is the disjoint union of two combinatorial classes (an object of
size `n` is a `B`-object of size `n` *or* a `C`-object of size `n`), then the
counting sequences add, `Aₙ = Bₙ + Cₙ`, and hence the OGFs add:

  **`(B + C)(z) = B(z) + C(z)`**   (part of F&S Theorem I.1).

The combinatorial content is the `Fintype.card` identity `counts_sum`; the
generating-function identity `ogf_sum` is its image under `ogfSeq`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- Counting sequences add: `(B + C)ₙ = Bₙ + Cₙ`. The genuine combinatorial fact,
from `Fintype.card_sum`. -/
@[simp] lemma CombClass.counts_sum (C D : CombClass) (n : ℕ) :
    (C.sum D).counts n = C.counts n + D.counts n :=
  Fintype.card_sum

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
theorem solution (C D : CombClass) :
    (C.sum D).ogf = C.ogf + D.ogf := by
  ext n
  simp [CombClass.counts_sum]
