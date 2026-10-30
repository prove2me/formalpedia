-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.ogf_prodPow
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:22.484107+00:00
-- url     : https://prove2.me/submissions/9d9cf57e-f4bb-47c7-8d45-583701522003

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_ProductPower
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.NatAntidiagonal

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

/-! ### Primitive classes

We encode the primitive classes with `Obj n := Fin (· n)` so that the `Fintype`
instance is uniform; their entire content is their counting sequence. -/

@[simp] lemma CombClass.counts_neutral (n : ℕ) :
    CombClass.neutral.counts n = if n = 0 then 1 else 0 :=
  Fintype.card_fin _

/-- `ε(z) = 1`. -/
lemma CombClass.ogf_neutral : CombClass.neutral.ogf = 1 := by
  ext n
  simp only [CombClass.coeff_ogf, CombClass.counts_neutral, coeff_one]
  by_cases h : n = 0 <;> simp [h]

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.2 — The Cartesian product construction

Flajolet & Sedgewick, Part A, Chapter I, §I.2, the product construction, the
heart of the symbolic method. If `A = B × C` (an object of size `n` is an
ordered pair `(β, γ)` with `|β| + |γ| = n`), then

  `Aₙ = ∑_{k=0}^{n} Bₖ · C_{n-k}`   (a convolution),

and therefore the OGFs multiply:

  **`(B × C)(z) = B(z) · C(z)`**   (part of F&S Theorem I.1).

The combinatorial content is the `Fintype.card` convolution identity
`counts_prod`, proved from `Fintype.card_sigma` / `Fintype.card_prod`. The
generating-function identity `ogf_prod` then follows from `PowerSeries.coeff_mul`
(the Cauchy product) after reconciling the `Finset.antidiagonal` indexing with
the `Fin (n+1)` indexing of the product class.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries Finset

/-- Counting sequences convolve: `(B × C)ₙ = ∑_{k≤n} Bₖ · C_{n-k}`. The genuine
combinatorial content, from `Fintype.card_sigma` and `Fintype.card_prod`. -/
@[simp] lemma CombClass.counts_prod (C D : CombClass) (n : ℕ) :
    (C.prod D).counts n = ∑ k : Fin (n + 1), C.counts k * D.counts (n - k) := by
  change Fintype.card (Σ k : Fin (n + 1), C.Obj k × D.Obj (n - k)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_prod]
  rfl

/-- **Product rule** (F&S Theorem I.1): `(B × C)(z) = B(z) · C(z)`. -/
theorem CombClass.ogf_prod (C D : CombClass) :
    (C.prod D).ogf = C.ogf * D.ogf := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_prod, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Fin.sum_univ_eq_sum_range (fun k => C.counts k * D.counts (n - k)) (n + 1)]
  push_cast
  simp [CombClass.coeff_ogf]

end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.2–I.3 — Cartesian powers and words over a finite alphabet

Flajolet & Sedgewick, Part A, Chapter I. Iterating the product construction gives
the `k`-fold Cartesian power `C^k = C × C × ⋯ × C`, with OGF `C(z)^k` (an immediate
induction from the binary product rule `ogf_prod`). As the standard application,
words of length `k` over an alphabet of `a` letters form `(a·Z)^k`, with OGF
`(a z)^k` (so there are `a^k` of them), recovering F&S §I.3.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

end AnalyticCombinatorics.Ch1

open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
theorem solution (C : CombClass) (k : ℕ) :
    (C.prodPow k).ogf = C.ogf ^ k := by
  set_option backward.isDefEq.respectTransparency false in
    induction k with
    | zero => simp [CombClass.prodPow, CombClass.ogf_neutral]
    | succ k ih => rw [CombClass.prodPow, CombClass.ogf_prod, ih, pow_succ']
