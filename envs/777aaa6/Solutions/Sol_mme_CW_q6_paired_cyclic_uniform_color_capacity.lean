-- Prove2me | solution 1 for mme_CW_q6_paired_cyclic_uniform_color_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-21T23:48:18.513985+00:00
-- url     : https://prove2.me/submissions/0251f065-84c5-426d-9359-0bca21a9ccb0

import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MME

private theorem uniform_restriction
    {N L G A H H' : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (outer : Finset (Fin A)) (P : Finset (Fin A × Fin H))
    (hH' : 0 < H')
    (hfiber : ∀ a ∈ outer,
      H' ≤ (Finset.univ.filter (fun h : Fin H => (a, h) ∈ P)).card)
    (hpaired : ∀ p0 ∈ P, ∀ p1 ∈ P, ∀ p2 ∈ P,
      family.PairedCyclicSupported halving p0 p1 p2 → p0 = p1 ∧ p1 = p2) :
    ∃ subfamily : CWQ6PrimaryHashFamily N L G outer.card H',
      ∃ split : subfamily.CommonBalancedXYHalving,
        split.position = halving.position ∧ subfamily.PairedCyclicInduced split := by
  classical
  let outerMap : Fin outer.card ↪ Fin A :=
    outer.equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have outer_mem (a : Fin outer.card) : outerMap a ∈ outer :=
    (outer.equivFin.symm a).property
  have inner_exists (a : Fin outer.card) :
      Nonempty (Fin H' ↪ {h : Fin H // (outerMap a, h) ∈ P}) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa [Fintype.card_subtype] using hfiber (outerMap a) (outer_mem a)
  let innerMap (a : Fin outer.card) : Fin H' ↪ Fin H :=
    (inner_exists a).some.trans (Function.Embedding.subtype _)
  let entryMap (p : Fin outer.card × Fin H') : Fin A × Fin H :=
    (outerMap p.1, innerMap p.1 p.2)
  have entry_mem (p : Fin outer.card × Fin H') : entryMap p ∈ P :=
    ((inner_exists p.1).some p.2).property
  have entry_injective : Function.Injective entryMap := by
    rintro ⟨a, h⟩ ⟨b, j⟩ heq
    have hab : a = b := outerMap.injective (congrArg Prod.fst heq)
    subst b
    have hhj : h = j := (innerMap a).injective (congrArg Prod.snd heq)
    subst j
    rfl
  let subfamily : CWQ6PrimaryHashFamily N L G outer.card H' :=
    { hHpos := hH'
      entry := fun p => family.entry (entryMap p)
      xInjective := family.xInjective.comp entry_injective
      yInjective := family.yInjective.comp entry_injective
      zSameFiber := fun a h j => family.zSameFiber (outerMap a) (innerMap a h) (innerMap a j)
      zSeparatesFibers := fun a b h j heq =>
        outerMap.injective (family.zSeparatesFibers _ _ _ _ heq)
      induced := fun p q r hs => by
        obtain ⟨hpq, hpr⟩ := family.induced (entryMap p) (entryMap q) (entryMap r) hs
        exact ⟨entry_injective hpq, outerMap.injective hpr⟩ }
  let split : subfamily.CommonBalancedXYHalving :=
    { half := halving.half
      even_length := halving.even_length
      position := halving.position
      first_x := fun p grade => halving.first_x (entryMap p) grade
      second_y := fun p grade => halving.second_y (entryMap p) grade }
  refine ⟨subfamily, split, rfl, ?_⟩
  intro p0 p1 p2 hs
  obtain ⟨h01, h12⟩ := hpaired (entryMap p0) (entry_mem p0)
    (entryMap p1) (entry_mem p1) (entryMap p2) (entry_mem p2) hs
  exact ⟨entry_injective h01, entry_injective h12⟩

/-- Two applications of pigeonhole recover uniform outer fibers inside one
color class. The inherited halving uses exactly the original positions. -/
theorem mme_CW_q6_paired_cyclic_uniform_color_extraction
    {N L G A H k : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (hk : 0 < k) (hkH : k ≤ H)
    (coloring : (family.pairedCyclicConflictGraph halving).Coloring (Fin k)) :
    ∃ A' : ℕ, A / k ≤ A' ∧
      ∃ subfamily : CWQ6PrimaryHashFamily N L G A' (H / k),
        ∃ split : subfamily.CommonBalancedXYHalving,
          split.position = halving.position ∧ subfamily.PairedCyclicInduced split := by
  classical
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have fiber_color (a : Fin A) :
      ∃ c : Fin k, H / k ≤ (Finset.univ.filter (fun h : Fin H => coloring (a, h) = c)).card :=
    Fintype.exists_le_card_fiber_of_mul_le_card
      (f := fun h => coloring (a, h)) (by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self H k)
  choose favorite hfavorite using fiber_color
  obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (f := favorite) (n := A / k) (by
      simpa [Nat.mul_comm] using Nat.div_mul_le_self A k)
  let outer := Finset.univ.filter (fun a => favorite a = c)
  let P := Finset.univ.filter (fun p : Fin A × Fin H => coloring p = c)
  have hfiber (a : Fin A) (ha : a ∈ outer) :
      H / k ≤ (Finset.univ.filter (fun h : Fin H => (a, h) ∈ P)).card := by
    have hac : favorite a = c := (Finset.mem_filter.mp ha).2
    simpa [P, hac] using hfavorite a
  have hpaired : ∀ p0 ∈ P, ∀ p1 ∈ P, ∀ p2 ∈ P,
      family.PairedCyclicSupported halving p0 p1 p2 → p0 = p1 ∧ p1 = p2 := by
    intro p0 hp0 p1 hp1 p2 hp2 hs
    have h0 : coloring p0 = c := (Finset.mem_filter.mp hp0).2
    have h1 : coloring p1 = c := (Finset.mem_filter.mp hp1).2
    have h2 : coloring p2 = c := (Finset.mem_filter.mp hp2).2
    by_contra hbad
    have eq_of_mem (p q : Fin A × Fin H)
        (hp : family.InPairedTriple p p0 p1 p2)
        (hq : family.InPairedTriple q p0 p1 p2)
        (heq : coloring p = coloring q) : p = q := by
      by_contra hne
      apply coloring.valid (show (family.pairedCyclicConflictGraph halving).Adj p q from ?_) heq
      exact ⟨hne, Or.inl ⟨p0, p1, p2, hs, hbad, hp, hq⟩⟩
    exact hbad ⟨eq_of_mem p0 p1 (Or.inl rfl) (Or.inr (Or.inl rfl)) (h0.trans h1.symm),
      eq_of_mem p1 p2 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (h1.trans h2.symm)⟩
  exact ⟨outer.card, hc, uniform_restriction family halving outer P
    (Nat.div_pos hkH hk) hfiber hpaired⟩

private theorem le_twice_mul_div {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) :
    n ≤ 2 * k * (n / k) := by
  have hpos := Nat.div_pos hkn hk
  have hmod := Nat.mod_lt n hk
  have hid := Nat.mod_add_div n k
  have hmul : k ≤ k * (n / k) := by
    simpa using Nat.mul_le_mul_left k hpos
  nlinarith

/-- Uniform paired-induced extraction with an explicit loss in the
`A³ H²` capacity used by the paired tensor construction. -/
theorem solution
    {N L G A H k : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hk : 0 < k) (hkA : k ≤ A) (hkH : k ≤ H)
    (coloring : (family.pairedCyclicConflictGraph halving).Coloring (Fin k)) :
    ∃ A' : ℕ, 0 < A' ∧ A / k ≤ A' ∧ 0 < H / k ∧
      A ^ 3 * H ^ 2 ≤ 32 * k ^ 5 * (A' ^ 3 * (H / k) ^ 2) ∧
      ∃ subfamily : CWQ6PrimaryHashFamily N L G A' (H / k),
        ∃ split : subfamily.CommonBalancedXYHalving,
          split.position = halving.position ∧ subfamily.PairedCyclicInduced split := by
  obtain ⟨A', hA', subfamily, split, hposition, hinduced⟩ :=
    mme_CW_q6_paired_cyclic_uniform_color_extraction family halving hk hkH coloring
  have ha : A ≤ 2 * k * A' :=
    (le_twice_mul_div hk hkA).trans (Nat.mul_le_mul_left (2 * k) hA')
  have hh : H ≤ 2 * k * (H / k) := le_twice_mul_div hk hkH
  refine ⟨A', (Nat.div_pos hkA hk).trans_le hA', hA', Nat.div_pos hkH hk,
    ?_, subfamily, split, hposition, hinduced⟩
  calc
    A ^ 3 * H ^ 2 ≤ (2 * k * A') ^ 3 * (2 * k * (H / k)) ^ 2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left ha 3) (Nat.pow_le_pow_left hh 2)
    _ = 32 * k ^ 5 * (A' ^ 3 * (H / k) ^ 2) := by ring
