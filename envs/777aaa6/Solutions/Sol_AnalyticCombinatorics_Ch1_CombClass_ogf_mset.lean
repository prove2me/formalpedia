-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.ogf_mset
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:33.357118+00:00
-- url     : https://prove2.me/submissions/cab0941e-54ba-4648-b661-49d1ecd23388

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Mset
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Sym.Card

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

/-- The counting identity for `MSET(C)`: `MSET(C)ₙ = ∑_{p:Partition n} ∏_m
multichoose(Cₘ, mult_m p)`, from `card_sigma`/`card_pi`/`card_sym_eq_multichoose`. -/
lemma CombClass.counts_mset (C : CombClass) (n : ℕ) :
    C.mset.counts n
      = ∑ p : Nat.Partition n, ∏ m : Fin (n + 1),
          (C.counts m.val).multichoose (p.parts.count m.val) := by
  classical
  change Fintype.card
      (Σ p : Nat.Partition n, ∀ m : Fin (n + 1), Sym (C.Obj m.val) (p.parts.count m.val)) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.card_pi]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Sym.card_sym_eq_multichoose]
  rfl

/-- The `MSET(C)` OGF is Mathlib's `genFun` of the multichoose family. -/
theorem CombClass.ogf_mset_eq_genFun (C : CombClass) :
    C.mset.ogf
      = Nat.Partition.genFun (R := ℚ) (fun m j => ((C.counts m).multichoose j : ℚ)) := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_mset, Nat.Partition.coeff_genFun, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsub : (p.parts.toFinsupp).support ⊆ Finset.range (n + 1) := by
    intro m hm
    rw [Multiset.toFinsupp_support, Multiset.mem_toFinset] at hm
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts hm))
  rw [Nat.cast_prod,
    Finsupp.prod_of_support_subset (p.parts.toFinsupp) hsub
      (fun m j => ((C.counts m).multichoose j : ℚ))
      (fun m _ => by simp),
    Fin.prod_univ_eq_prod_range
      (fun m => ((C.counts m).multichoose (p.parts.count m) : ℚ)) (n + 1)]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Multiset.toFinsupp_apply]

section EulerProduct

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatMset

local instance instDiscRatMset : DiscreteTopology ℚ := ⟨rfl⟩

end EulerProduct
end AnalyticCombinatorics.Ch1

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatMset
attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instDiscRatMset
open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology
theorem solution (C : CombClass) :
    C.mset.ogf
      = ∏' i, ∑' k, ((C.counts (i + 1)).multichoose k : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * k) := by
  rw [CombClass.ogf_mset_eq_genFun, Nat.Partition.genFun_eq_tprod]
  refine tprod_congr fun i => ?_
  have hshift : Summable
      (fun j => ((C.counts (i + 1)).multichoose (j + 1) : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * (j + 1))) :=
    Nat.Partition.summable_genFun_term (fun m j => ((C.counts m).multichoose j : ℚ)) i
  have hsumm : Summable
      (fun k => ((C.counts (i + 1)).multichoose k : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * k)) :=
    by
      set_option backward.isDefEq.respectTransparency false in
        exact (summable_nat_add_iff 1).mp hshift
  set_option backward.isDefEq.respectTransparency false in
    rw [hsumm.tsum_eq_zero_add]
  set_option backward.isDefEq.respectTransparency false in
    simp [Nat.multichoose_zero_right]
