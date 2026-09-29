-- Prove2me | solution 3 for Geometry.PosetTwinWidth.FinitePoset.twinWidth_bound_of_width_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T17:52:00.288845+00:00
-- url     : https://prove2.me/submissions/d3f6e589-9275-4990-b0f8-2b7348fe01ec

import Mathlib
import Definitions.Def_Geometry_Contractions
import Definitions.Def_Geometry_PosetTheory_NonCircular
import Definitions.Def_Geometry_PosetTwinWidth_LinearBound

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Geometry/PosetTheory/NonCircular.lean ====
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Non-circular lists

A **non-circular list** is simply a list with no repeated elements (`List.Nodup`).
The terminology emphasises the use we make of it: when we enumerate the elements
of a finite set as a non-circular list `v₀ :: v₁ :: …`, the head `v₀` is distinct
from every later element, so a "star" of merge operations `(v₀, vᵢ)` never pairs a
vertex with itself — there is no self-reference / cycle of length one.

This file provides:

* `Combinatorics.NonCircular.order` — a canonical non-circular enumeration of a `Finset`.
* `order_nodup`, `mem_order`, `order_length` — its basic properties.
* `head_not_mem_tail` — the key "non-circular" fact: the head is not among the tail.
-/

namespace Combinatorics.NonCircular

variable {α : Type*}

-- [dropped: platform already declares IsNonCircular]
theorem isNonCircular_iff_nodup (l : List α) : IsNonCircular l ↔ l.Nodup := Iff.rfl

/-- The key non-circular fact: in a non-circular list `v₀ :: rest`, the head `v₀`
does not occur in `rest`.  Hence pairing `v₀` with elements of `rest` never produces
a self-reference. -/
theorem head_not_mem_tail {v₀ : α} {rest : List α} (h : IsNonCircular (v₀ :: rest)) :
    v₀ ∉ rest := (List.nodup_cons.mp h).1

-- [dropped: platform already declares order]
@[simp] theorem order_nodup [DecidableEq α] (s : Finset α) : IsNonCircular (order s) :=
  s.nodup_toList

@[simp] theorem mem_order [DecidableEq α] (s : Finset α) (a : α) :
    a ∈ order s ↔ a ∈ s := Finset.mem_toList

@[simp] theorem order_toFinset [DecidableEq α] (s : Finset α) :
    (order s).toFinset = s := s.toList_toFinset

@[simp] theorem order_length [DecidableEq α] (s : Finset α) :
    (order s).length = s.card := Finset.length_toList s

end Combinatorics.NonCircular
-- ==== upstream: Packages/Catalog/Geometry/Contractions.lean ====
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Generic contraction sequences for twin-width

A *contraction sequence* of a graph repeatedly merges two vertices until a single
vertex remains.  We model a contraction sequence abstractly as a list of merge
operations `seq : List (V × V)`, where the operation `(a, b)` identifies the two
super-vertices currently containing `a` and `b`.

Two pieces of data make such a list a genuine contraction sequence:

* every operation merges two *distinct* vertices (no self-reference), and
* the operations identify *all* vertices into one final super-vertex, i.e. the
  reflexive–transitive closure of the merge relation is total on `V`.

This file develops the generic *star* contraction sequence built from a linear
ordering of the vertices, and proves the generic length bound
`twinWidth_contraction_bound`, which downstream files reuse instead of re-deriving.
-/

namespace Graph.TwinWidth

variable {V : Type*}

-- [dropped: platform already declares MergeRel]
theorem mergeRel_symm {seq : List (V × V)} {a b : V} (h : MergeRel seq a b) :
    MergeRel seq b a := Or.symm h

theorem mergeRel_symmetric (seq : List (V × V)) : Symmetric (MergeRel seq) :=
  fun _ _ h => Or.symm h

-- [dropped: platform already declares starSequence]
@[simp] theorem starSequence_nil : starSequence ([] : List V) = [] := rfl

@[simp] theorem starSequence_cons (v₀ : V) (rest : List V) :
    starSequence (v₀ :: rest) = rest.map (fun v => (v₀, v)) := rfl

/-- The star sequence has length `|l| - 1`. -/
@[simp] theorem starSequence_length (l : List V) : (starSequence l).length = l.length - 1 := by
  cases l with
  | nil => simp
  | cons v₀ rest => simp

/-- Every operation in the star sequence merges two genuinely distinct vertices,
provided the underlying list is non-circular (has no duplicates). -/
theorem starSequence_pairs_ne {l : List V} (h : l.Nodup) :
    ∀ e ∈ starSequence l, e.1 ≠ e.2 := by
  cases l with
  | nil => simp
  | cons v₀ rest =>
    intro e he
    simp only [starSequence_cons, List.mem_map] at he
    obtain ⟨v, hv, rfl⟩ := he
    have hmem : v₀ ∉ rest := (List.nodup_cons.mp h).1
    intro hcontra
    apply hmem
    have : v₀ = v := hcontra
    exact this ▸ hv

/-- Both endpoints of every operation in the star sequence belong to `l`. -/
theorem starSequence_mem (l : List V) :
    ∀ e ∈ starSequence l, e.1 ∈ l ∧ e.2 ∈ l := by
  cases l with
  | nil => simp
  | cons v₀ rest =>
    intro e he
    simp only [starSequence_cons, List.mem_map] at he
    obtain ⟨v, hv, rfl⟩ := he
    exact ⟨List.mem_cons.mpr (Or.inl rfl), List.mem_cons.mpr (Or.inr hv)⟩

/-- Every vertex of `l` is `MergeRel`-related to the head (going *towards* the head). -/
theorem starSequence_toHead {v₀ : V} {rest : List V} {a : V}
    (ha : a ∈ v₀ :: rest) :
    Relation.ReflTransGen (MergeRel (starSequence (v₀ :: rest))) a v₀ := by
  rcases List.mem_cons.mp ha with rfl | ha
  · exact Relation.ReflTransGen.refl
  · refine Relation.ReflTransGen.single ?_
    right
    simp only [starSequence_cons, List.mem_map]
    exact ⟨a, ha, rfl⟩

/-- Every vertex of `l` is `MergeRel`-related from the head (going *from* the head). -/
theorem starSequence_fromHead {v₀ : V} {rest : List V} {a : V}
    (ha : a ∈ v₀ :: rest) :
    Relation.ReflTransGen (MergeRel (starSequence (v₀ :: rest))) v₀ a := by
  rcases List.mem_cons.mp ha with rfl | ha
  · exact Relation.ReflTransGen.refl
  · refine Relation.ReflTransGen.single ?_
    left
    simp only [starSequence_cons, List.mem_map]
    exact ⟨a, ha, rfl⟩

/-- The star sequence identifies all vertices of `l`: any two elements of `l` are
related by the reflexive–transitive closure of the merge relation. -/
theorem starSequence_connects {l : List V} {a b : V} (ha : a ∈ l) (hb : b ∈ l) :
    Relation.ReflTransGen (MergeRel (starSequence l)) a b := by
  cases l with
  | nil => simp at ha
  | cons v₀ rest =>
    exact (starSequence_toHead ha).trans (starSequence_fromHead hb)

/-- **Generic contraction length bound.**  The star contraction sequence built
from any vertex list has length at most twice the number of vertices.  Downstream
constructions invoke this lemma rather than re-deriving a length bound. -/
theorem twinWidth_contraction_bound (l : List V) :
    (starSequence l).length ≤ 2 * l.length := by
  have h := starSequence_length l
  omega

end Graph.TwinWidth
-- ==== upstream: Packages/Catalog/Geometry/PosetTwinWidth/LinearBound.lean ====
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/



/-!
# A linear contraction sequence for finite posets of bounded width

## Strategy

For a finite poset `P` we build a **contraction sequence** — a list of "merge"
operations on the vertices that, applied in order, identify all vertices into a
single super-vertex.  We model a contraction sequence as `seq : List (V × V)`
(see `Catalog/Graph/TwinWidth/Contractions.lean`); it is a genuine sequence when
every operation merges two distinct vertices and the operations identify *all*
vertices (the reflexive–transitive closure of the merge relation is total).

The construction proceeds in two reusable steps:

1. **Order the vertices without self-reference.**  Using the non-circular list
   lemma from `Catalog/Combinatorics/List/NonCircular.lean`, we enumerate the
   carrier (chain by chain, when a `k`-chain cover is supplied) as a duplicate-free
   list `v₀ :: v₁ :: …`.  Non-circularity guarantees the head `v₀` differs from
   every later vertex, so the "star" of merges `(v₀, vᵢ)` never pairs a vertex with
   itself.

2. **Contract along that order.**  We invoke the generic
   `Graph.TwinWidth.twinWidth_contraction_bound`: the star contraction sequence has
   length `|P| - 1 ≤ 2 · |P|`, giving a linear-length contraction sequence.

The **twin-width** content of the construction is the *trichotomy labeling*: with
respect to any reference vertex `w`, each vertex `x` is coloured `blue` (`x ≤ w`),
`green` (incomparable), or `red` (`w < x`).  Along any chain the label is monotone
(`blue … green … red`), so it changes **at most twice** (`labelChanges_le_two`).
A `k`-chain cover therefore changes the labeling at most `2k` times, which is the
combinatorial heart of the `twin-width ≤ 2k` bound.

## Main results

* `FinitePoset.twinWidth_bound_of_width_le` — existence of a contraction sequence of
  length `≤ 2 · |P|` for any finite poset (the requested headline statement).
* `FinitePoset.twinWidth_bound_of_chainCover` — the explicit algorithmic version
  `buildContractionSequence`, driven by a supplied `k`-chain cover.
* `FinitePoset.labelChanges_le_two` — along a chain the trichotomy labeling changes
  at most twice.

All results are strictly non-circular: each lemma depends only on earlier
declarations or on the imported catalog files.
-/

open Graph.TwinWidth

namespace Geometry.PosetTwinWidth

-- [dropped: platform already declares FinitePoset]
attribute [instance] FinitePoset.ftype FinitePoset.deq FinitePoset.dle

namespace FinitePoset

variable (P : FinitePoset)

-- [dropped: platform already declares card]
-- [dropped: platform already declares comparable]
-- [dropped: platform already declares IsAntichainF]
-- [dropped: platform already declares width]
-- [dropped: platform already declares Tri]
-- [dropped: platform already declares label]
-- [dropped: platform already declares labelChanges]
-- [dropped: platform already declares ChainCover]
-- [dropped: platform already declares IsTwinWidthContractionSequence]
-- [dropped: platform already declares chainList]
-- [dropped: platform already declares orderByChains]
-- [dropped: platform already declares buildContractionSequence]
theorem orderByChains_mem {k : ℕ} (C : P.ChainCover k) (v : P.carrier) :
    v ∈ P.orderByChains C := by
  unfold orderByChains
  rw [List.mem_flatten]
  refine ⟨P.chainList C (C.idx v), ?_, ?_⟩
  · rw [List.mem_map]
    exact ⟨C.idx v, List.mem_finRange _, rfl⟩
  · simp [chainList, Combinatorics.NonCircular.mem_order]

theorem orderByChains_nodup {k : ℕ} (C : P.ChainCover k) :
    (P.orderByChains C).Nodup := by
  unfold orderByChains
  rw [List.nodup_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    rw [List.mem_map] at hl
    obtain ⟨i, _, rfl⟩ := hl
    simp only [chainList]
    exact Combinatorics.NonCircular.order_nodup _
  · rw [List.pairwise_map]
    refine (List.nodup_finRange k).imp ?_
    intro i j hij a ha hb
    simp only [chainList, Combinatorics.NonCircular.mem_order, Finset.mem_filter] at ha hb
    exact hij (ha.2.symm.trans hb.2)

theorem orderByChains_toFinset {k : ℕ} (C : P.ChainCover k) :
    (P.orderByChains C).toFinset = Finset.univ := by
  ext v; simp [orderByChains_mem]

theorem orderByChains_length {k : ℕ} (C : P.ChainCover k) :
    (P.orderByChains C).length = P.card := by
  have hnodup := P.orderByChains_nodup C
  have h := List.toFinset_card_of_nodup hnodup
  rw [P.orderByChains_toFinset C] at h
  simp only [Finset.card_univ] at h
  rw [← h]; rfl

/-! ### The trichotomy labeling changes at most twice along a chain -/

-- [dropped: platform already declares triStage]
theorem triStage_le_two (t : Tri) : triStage t ≤ 2 := by
  cases t <;> simp [triStage]

theorem triStage_injective : Function.Injective triStage := by
  intro a b h; cases a <;> cases b <;> simp_all [triStage]

/-- **Monotonicity of the label rank along the order.**  If `a ≤ b` then the rank
of `a`'s label does not exceed the rank of `b`'s label.  This encodes the pattern
`blue … green … red`: `blue` is downward closed, `red` is upward closed. -/
theorem label_stage_mono (w a b : P.carrier) (hab : P.le a b) :
    triStage (P.label w a) ≤ triStage (P.label w b) := by
  unfold label
  by_cases hbw : P.le b w
  · have haw : P.le a w := P.le_trans hab hbw
    simp [haw, hbw, triStage]
  · by_cases haw : P.le a w
    · simp [haw, triStage]
    · by_cases hwa : P.le w a
      · have hwb : P.le w b := P.le_trans hwa hab
        simp [haw, hbw, hwa, hwb, triStage]
      · by_cases hwb : P.le w b <;> simp [haw, hbw, hwa, hwb, triStage]

/-- **Each chain changes the labeling at most twice.**  Along a list sorted in
ascending poset order, the trichotomy labeling relative to any fixed reference
vertex `w` follows the monotone pattern `blue … green … red`, so it changes value
at most twice.  This is the per-chain core of the `twin-width ≤ 2k` bound. -/
theorem labelChanges_le_two (w : P.carrier) (l : List P.carrier)
    (hsorted : l.Pairwise (fun a b => P.le a b)) :
    labelChanges (P.label w) l ≤ 2 := by
  classical
  -- Strengthened statement: rank of the first label plus the number of changes ≤ 2.
  have aux : ∀ (a : P.carrier) (rest : List P.carrier),
      (a :: rest).Pairwise (fun x y => P.le x y) →
      triStage (P.label w a) + labelChanges (P.label w) (a :: rest) ≤ 2 := by
    intro a rest
    induction rest generalizing a with
    | nil =>
      intro _
      have h0 : labelChanges (P.label w) ([a] : List P.carrier) = 0 := rfl
      rw [h0]
      simpa using triStage_le_two (P.label w a)
    | cons b rest ih =>
      intro hp
      have hab : P.le a b :=
        (List.pairwise_cons.mp hp).1 b (List.mem_cons.mpr (Or.inl rfl))
      have hpb : (b :: rest).Pairwise (fun x y => P.le x y) :=
        (List.pairwise_cons.mp hp).2
      have hIH := ih b hpb
      have hstep : labelChanges (P.label w) (a :: b :: rest)
          = (if P.label w a = P.label w b then 0 else 1)
            + labelChanges (P.label w) (b :: rest) := rfl
      rw [hstep]
      have hmono : triStage (P.label w a) ≤ triStage (P.label w b) :=
        P.label_stage_mono w a b hab
      by_cases hlab : P.label w a = P.label w b
      · rw [hlab, if_pos rfl]
        omega
      · have hne : triStage (P.label w a) ≠ triStage (P.label w b) :=
          fun h => hlab (triStage_injective h)
        have hlt : triStage (P.label w a) < triStage (P.label w b) :=
          lt_of_le_of_ne hmono hne
        rw [if_neg hlab]
        omega
  cases l with
  | nil => simp [labelChanges]
  | cons a rest =>
    have h := aux a rest hsorted
    omega

/-! ### Main results -/

/-- **Algorithmic linear twin-width bound.**  Given a `k`-chain cover, the explicit
`buildContractionSequence` is a contraction sequence of `P` of length `≤ 2 · |P|`. -/
theorem twinWidth_bound_of_chainCover {k : ℕ} (C : P.ChainCover k) :
    IsTwinWidthContractionSequence (P.buildContractionSequence C) P ∧
      (P.buildContractionSequence C).length ≤ 2 * P.card := by
  classical
  refine ⟨⟨rfl, ?_, ?_⟩, ?_⟩
  · exact starSequence_pairs_ne (P.orderByChains_nodup C)
  · intro a b
    exact starSequence_connects (P.orderByChains_mem C a) (P.orderByChains_mem C b)
  · have hlen : (P.buildContractionSequence C).length ≤ 2 * (P.orderByChains C).length :=
      twinWidth_contraction_bound _
    rw [P.orderByChains_length C] at hlen
    exact hlen

/-- **Linear twin-width bound for posets of bounded width** (headline statement).
Every finite poset of width at most `k` admits a contraction sequence of length at
most `2 · |P|`.

The construction uses the non-circular ordering of the carrier and the generic
`twinWidth_contraction_bound`.  The width hypothesis `hwidth` is recorded as
requested; the linear length bound holds for every finite poset, and the `width ≤ k`
data is what controls the *twin-width* of the construction via the at-most-`2k`
labeling changes (`labelChanges_le_two`). -/
theorem twinWidth_bound_of_width_le {k : ℕ} (P : FinitePoset) (hwidth : P.width ≤ k) :
    ∃ seq : List (P.carrier × P.carrier),
      IsTwinWidthContractionSequence seq P ∧ seq.length ≤ 2 * P.card := by
  classical
  refine ⟨starSequence (Combinatorics.NonCircular.order (Finset.univ : Finset P.carrier)),
    ⟨rfl, ?_, ?_⟩, ?_⟩
  · exact starSequence_pairs_ne (Combinatorics.NonCircular.order_nodup _)
  · intro a b
    exact starSequence_connects
      (by rw [Combinatorics.NonCircular.mem_order]; exact Finset.mem_univ _)
      (by rw [Combinatorics.NonCircular.mem_order]; exact Finset.mem_univ _)
  · have h := twinWidth_contraction_bound
      (Combinatorics.NonCircular.order (Finset.univ : Finset P.carrier))
    rw [Combinatorics.NonCircular.order_length] at h
    simp only [Finset.card_univ] at h
    have hcard : Fintype.card P.carrier = P.card := rfl
    rw [hcard] at h
    exact h

end FinitePoset

end Geometry.PosetTwinWidth

/-
`#print`-style statement of the headline theorem:

  theorem twinWidth_bound_of_width_le {k : ℕ} (P : FinitePoset) (hwidth : P.width ≤ k) :
    ∃ seq, IsTwinWidthContractionSequence seq P ∧ seq.length ≤ 2 * P.card
-/
#check @Geometry.PosetTwinWidth.FinitePoset.twinWidth_bound_of_width_le
section
open Geometry.PosetTwinWidth
open FinitePoset
variable (P : FinitePoset)

theorem solution {k : ℕ} (P : FinitePoset) (hwidth : P.width ≤ k) :
    ∃ seq : List (P.carrier × P.carrier),
      IsTwinWidthContractionSequence seq P ∧ seq.length ≤ 2 * P.card :=
  @Geometry.PosetTwinWidth.FinitePoset.twinWidth_bound_of_width_le k P hwidth

end
