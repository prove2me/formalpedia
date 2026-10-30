-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.ogf_partitions
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:31.170525+00:00
-- url     : https://prove2.me/submissions/891d1650-7375-47b0-870b-956e40124e40

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Partitions
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.Partition.GenFun

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
# Ch1 §I.3 — Integer partitions and Euler's product (MSET flagship)

Flajolet & Sedgewick, Part A, Chapter I, §I.3. An integer partition of `n` is a
multiset of positive integers summing to `n` — i.e. an object of `MSET(ℙ)` of size
`n`. Its generating function is Euler's product

  `P(z) = ∏_{m≥1} 1/(1 - z^m) = ∏_{m≥1} ∑_{j≥0} z^{m j}`.

We model the partition class with Mathlib's `Nat.Partition` (a `Fintype`), connect
its OGF to Mathlib's `Nat.Partition.genFun`, and push it to the explicit infinite
product. The literal Euler product is an explicit TODO in Mathlib's `GenFun`, so
this is genuinely new content; it is anchored on `#(Nat.Partition n)`. The infinite
product/sums use the X-adic (coefficientwise) topology on `ℚ⟦X⟧`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

/-- The partition OGF is Mathlib's `genFun` of the constant family `1` (both are
`∑ₙ #(Partition n) zⁿ`). -/
theorem CombClass.ogf_partitions_eq_genFun :
    CombClass.partitions.ogf = Nat.Partition.genFun (R := ℚ) (fun _ _ => 1) := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_partitions, Nat.Partition.coeff_genFun]
  simp [Finsupp.prod]

section EulerProduct

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatPartitions

local instance instDiscRatPartitions : DiscreteTopology ℚ := ⟨rfl⟩

end EulerProduct
end AnalyticCombinatorics.Ch1

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatPartitions
attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instDiscRatPartitions
open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology
theorem solution :
    CombClass.partitions.ogf
      = ∏' i, ∑' j, (X : ℚ⟦X⟧) ^ ((i + 1) * j) := by
  rw [CombClass.ogf_partitions_eq_genFun, Nat.Partition.genFun_eq_tprod]
  refine tprod_congr fun i => ?_
  have hcc : constantCoeff (R := ℚ) (X ^ (i + 1)) = 0 := by
    rw [map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.succ_ne_zero i)]
  have hsumm : Summable fun j => (X : ℚ⟦X⟧) ^ ((i + 1) * j) := by
    simpa [pow_mul] using summable_pow_of_constantCoeff_eq_zero hcc
  set_option backward.isDefEq.respectTransparency false in
    rw [hsumm.tsum_eq_zero_add]
  set_option backward.isDefEq.respectTransparency false in
    simp [one_smul]
