-- Prove2me | solution 1 for AnalyticCombinatorics.Ch1.CombClass.ogf_pset_posInt
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T12:34:37.758454+00:00
-- url     : https://prove2.me/submissions/1b785d25-8b3f-483d-9eaa-e58d72c14ffb

import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Sequence
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_Pset
import Definitions.Def_AnalyticCombinatorics_Ch1_OGF_DistinctPartitions
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.Fintype.Powerset
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

@[simp] lemma CombClass.counts_posInt (n : ℕ) :
    CombClass.posInt.counts n = if 0 < n then 1 else 0 :=
  Fintype.card_fin _

end AnalyticCombinatorics.Ch1

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

/-- The counting identity for `PSET(C)`: `PSET(C)ₙ = ∑_{p:Partition n} ∏_m
choose(Cₘ, mult_m p)`, from `card_sigma`/`card_pi`/`card_finset_len`. -/
lemma CombClass.counts_pset (C : CombClass) (n : ℕ) :
    C.pset.counts n
      = ∑ p : Nat.Partition n, ∏ m : Fin (n + 1),
          (C.counts m.val).choose (p.parts.count m.val) := by
  classical
  change Fintype.card
      (Σ p : Nat.Partition n,
        ∀ m : Fin (n + 1), { s : Finset (C.Obj m.val) // s.card = p.parts.count m.val }) = _
  rw [Fintype.card_sigma]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Fintype.card_pi]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Fintype.card_finset_len]
  rfl

/-- The `PSET(C)` OGF is Mathlib's `genFun` of the binomial family. -/
theorem CombClass.ogf_pset_eq_genFun (C : CombClass) :
    C.pset.ogf
      = Nat.Partition.genFun (R := ℚ) (fun m j => ((C.counts m).choose j : ℚ)) := by
  ext n
  rw [CombClass.coeff_ogf, CombClass.counts_pset, Nat.Partition.coeff_genFun, Nat.cast_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hsub : (p.parts.toFinsupp).support ⊆ Finset.range (n + 1) := by
    intro m hm
    rw [Multiset.toFinsupp_support, Multiset.mem_toFinset] at hm
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.Partition.le_of_mem_parts hm))
  rw [Nat.cast_prod,
    Finsupp.prod_of_support_subset (p.parts.toFinsupp) hsub
      (fun m j => ((C.counts m).choose j : ℚ))
      (fun m _ => by simp),
    Fin.prod_univ_eq_prod_range
      (fun m => ((C.counts m).choose (p.parts.count m) : ℚ)) (n + 1)]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [Multiset.toFinsupp_apply]

section EulerProduct

open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatPset

local instance instDiscRatPset : DiscreteTopology ℚ := ⟨rfl⟩

/-- **The powerset construction as an infinite product** (F&S Theorem I.1): for a
class `C` with `C₀=∅`, `PSET(C)(z) = ∏_{i} (∑_{k} choose(Cᵢ₊₁, k) z^{(i+1)k})`,
i.e. `∏_{m≥1} (1 + z^m)^{Cₘ}`. -/
theorem CombClass.ogf_pset (C : CombClass) :
    C.pset.ogf
      = ∏' i, ∑' k, ((C.counts (i + 1)).choose k : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * k) := by
  rw [CombClass.ogf_pset_eq_genFun, Nat.Partition.genFun_eq_tprod]
  refine tprod_congr fun i => ?_
  have hshift : Summable
      (fun j => ((C.counts (i + 1)).choose (j + 1) : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * (j + 1))) :=
    Nat.Partition.summable_genFun_term (fun m j => ((C.counts m).choose j : ℚ)) i
  have hsumm : Summable
      (fun k => ((C.counts (i + 1)).choose k : ℚ) • (X : ℚ⟦X⟧) ^ ((i + 1) * k)) :=
    by
      set_option backward.isDefEq.respectTransparency false in
        exact (summable_nat_add_iff 1).mp hshift
  set_option backward.isDefEq.respectTransparency false in
    rw [hsumm.tsum_eq_zero_add]
  set_option backward.isDefEq.respectTransparency false in
    simp

end EulerProduct
end AnalyticCombinatorics.Ch1

/-!
# Ch1 §I.3 — Partitions into distinct parts (PSET flagship)

Flajolet & Sedgewick, Part A, Chapter I, §I.3. A partition of `n` into *distinct*
parts is a set of distinct positive integers summing to `n` — an object of
`PSET(ℙ)` of size `n`. Specializing the general powerset transfer `ogf_pset` to the
positive-integer class `ℙ` (`Cₘ=1`, `choose 1 k` supported on `{0,1}`) gives the
classical generating function

  `D(z) = ∏_{m≥1} (1 + z^m)`.
-/

namespace AnalyticCombinatorics.Ch1

open PowerSeries

section
open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatDistinct

local instance instDiscRatDistinct : DiscreteTopology ℚ := ⟨rfl⟩

end
end AnalyticCombinatorics.Ch1

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instTopRatDistinct
attribute [local instance] _root_.AnalyticCombinatorics.Ch1.instDiscRatDistinct
open AnalyticCombinatorics AnalyticCombinatorics.Ch1
open PowerSeries
open scoped PowerSeries.WithPiTopology
open PowerSeries.WithPiTopology
theorem solution :
    CombClass.posInt.pset.ogf = ∏' i, (1 + (X : ℚ⟦X⟧) ^ (i + 1)) := by
  set_option backward.isDefEq.respectTransparency false in
    rw [CombClass.ogf_pset]
    refine tprod_congr fun i => ?_
    have hc : CombClass.posInt.counts (i + 1) = 1 := by simp [CombClass.counts_posInt]
    rw [hc, tsum_eq_sum (s := {0, 1}) (fun k hk => ?_)]
    · rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
      simp
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]
