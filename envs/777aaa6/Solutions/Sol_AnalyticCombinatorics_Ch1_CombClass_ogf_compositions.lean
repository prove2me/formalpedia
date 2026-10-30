-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.ogf_compositions
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-24T21:23:39.119979+00:00
-- url     : https://prove2.me/submissions/a5494888-36bc-405e-87c1-531de4f8729d

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.Composition

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
# Ch1 §I.2 / §I.3 — The sequence construction and integer compositions

Flajolet & Sedgewick, Part A, Chapter I. The sequence construction `SEQ(C)` forms
all finite sequences `(γ₁, …, γₘ)` of `C`-objects, with size the sum of the
component sizes. For this to give a (finite) combinatorial class one needs `C` to
have no object of size `0` (F&S's standing side-condition); the positive
component sizes of a size-`n` sequence then form a *composition* of `n`, so we
model `SEQ(C)` over Mathlib's `Composition n`.

This file proves, at the level of counting sequences, the genuine combinatorial
content:

* `counts_seq` — `(SEQ C)ₙ = ∑_{compositions c of n} ∏ᵢ C_{cᵢ}`.
* `counts_seq_posInt` — **integer compositions are sequences of positive
  integers** (F&S §I.3): `(SEQ ℙ)ₙ = #(Composition n) = 2^{n-1}`.

The closed-form generating function of compositions lives in `Compositions.lean`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

@[simp] lemma CombClass.counts_compositions (n : ℕ) :
    CombClass.compositions.counts n = 2 ^ (n - 1) :=
  composition_card n

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.3 — The generating function of integer compositions

Flajolet & Sedgewick, Part A, Chapter I, §I.3. There are `2^{n-1}` compositions
of `n ≥ 1` (Mathlib's `composition_card`), so their ordinary generating function
is

  `C(z) = ∑ₙ 2^{n-1} zⁿ = (1 - z)/(1 - 2z)`,

which we state in polynomial form as `C(z)·(1 - 2z) = 1 - z`. Mathlib has the
counting result but not this generating function, so the identity is new content;
it is the closed form predicted by the symbolic method via `compositions = SEQ(ℙ)`
(see `counts_seq_posInt` in `Sequence.lean`).
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

@[simp] lemma CombClass.coeff_ogf_compositions (n : ℕ) :
    coeff n CombClass.compositions.ogf = (2 ^ (n - 1) : ℚ) := by
  rw [CombClass.coeff_ogf, CombClass.counts_compositions]
  push_cast
  ring

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
theorem solution :
    CombClass.compositions.ogf * (1 - 2 * X) = 1 - X := by
  have expand : CombClass.compositions.ogf * (1 - 2 * X)
      = CombClass.compositions.ogf
        - CombClass.compositions.ogf * X - CombClass.compositions.ogf * X := by
        set_option backward.isDefEq.respectTransparency false in
          ring
  rw [expand]
  ext n
  rcases n with _ | _ | k
  · -- n = 0
    simp [map_sub, coeff_zero_eq_constantCoeff, map_mul, constantCoeff_X]
  · -- n = 1
    simp [map_sub, coeff_succ_mul_X, coeff_one, coeff_X]
  · -- n = k + 2
    simp only [map_sub, coeff_succ_mul_X, CombClass.coeff_ogf_compositions,
      coeff_one, coeff_X, Nat.add_sub_cancel, pow_succ]
    norm_num
    ring
