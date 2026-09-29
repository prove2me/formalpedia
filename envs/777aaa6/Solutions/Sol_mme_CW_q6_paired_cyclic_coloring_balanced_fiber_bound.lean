-- Prove2me | solution 1 for mme_CW_q6_paired_cyclic_coloring_balanced_fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-21T23:56:31.858985+00:00
-- url     : https://prove2.me/submissions/53b53459-f152-47ed-9ebf-9acaea9ec1ec

import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open MME

private theorem supported_at
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (p : Fin A × Fin H) (j : Fin (2 * N)) :
    CWQ6CoupledLocalSupported
      ((family.entry p).val 0 j) ((family.entry p).val 1 j)
      ((family.entry p).val 2 j) :=
  (family.entry p).property.1 j

/-- Paired inducedness forces each outer fiber to be injective under
restriction of its Y address to the first half. -/
theorem mme_CW_q6_paired_cyclic_first_half_y_injective
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hinduced : family.PairedCyclicInduced halving) (a : Fin A) :
    Function.Injective (fun h : Fin H => fun r : Fin N =>
      (family.entry (a, h)).val 1 (halving.position (Sum.inl r))) := by
  intro h j heq
  have hs : family.PairedCyclicSupported halving (a, h) (a, j) (a, j) := by
    constructor
    · intro r
      have heqr := congrFun heq r
      dsimp at heqr
      rw [heqr]
      exact supported_at family (a, j) _
    · intro r
      rw [family.zSameFiber a h j]
      exact supported_at family (a, j) _
  exact congrArg Prod.snd (hinduced _ _ _ hs).1

/-- The complementary collision condition forces injectivity of the
second-half X address within every outer fiber. -/
theorem mme_CW_q6_paired_cyclic_second_half_x_injective
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hinduced : family.PairedCyclicInduced halving) (a : Fin A) :
    Function.Injective (fun h : Fin H => fun r : Fin N =>
      (family.entry (a, h)).val 0 (halving.position (Sum.inr r))) := by
  intro h j heq
  have hs : family.PairedCyclicSupported halving (a, j) (a, h) (a, j) := by
    constructor
    · intro r
      rw [family.zSameFiber a h j]
      exact supported_at family (a, j) _
    · intro r
      have heqr := congrFun heq r
      dsimp at heqr
      rw [heqr]
      exact supported_at family (a, j) _
  exact congrArg Prod.snd (hinduced _ _ _ hs).2

/-- Only binary Y words occur, so paired inducedness imposes a half-word
cardinality bound on each nonempty collection of outer fibers. -/
theorem mme_CW_q6_paired_cyclic_induced_fiber_bound
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (hinduced : family.PairedCyclicInduced halving) (hA : 0 < A) :
    H ≤ 2 ^ N := by
  let a : Fin A := ⟨0, hA⟩
  have y_binary (h : Fin H) (r : Fin N) :
      ((family.entry (a, h)).val 1 (halving.position (Sum.inl r))).val < 2 := by
    have hs := supported_at family (a, h) (halving.position (Sum.inl r))
    rcases hs with ⟨_, hy, _⟩ | ⟨_, hy, _⟩ | ⟨_, hy, _⟩ | ⟨_, hy, _⟩ <;>
      simp [hy]
  let word (h : Fin H) (r : Fin N) : Fin 2 :=
    ⟨((family.entry (a, h)).val 1 (halving.position (Sum.inl r))).val, y_binary h r⟩
  have hinj : Function.Injective word := by
    intro h j heq
    apply mme_CW_q6_paired_cyclic_first_half_y_injective family halving hinduced a
    funext r
    apply Fin.ext
    exact congrArg (fun v : Fin 2 => v.val) (congrFun heq r)
  simpa using Fintype.card_le_of_injective word hinj

/-- A color and a first-half Y word determine at most one entry of a fixed
outer fiber. Thus a large fiber imposes a lower bound on the color count. -/
theorem mme_CW_q6_paired_cyclic_coloring_fiber_bound
    {N L G A H k : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (hA : 0 < A)
    (coloring : (family.pairedCyclicConflictGraph halving).Coloring (Fin k)) :
    H ≤ k * 2 ^ N := by
  let a : Fin A := ⟨0, hA⟩
  have y_binary (h : Fin H) (r : Fin N) :
      ((family.entry (a, h)).val 1 (halving.position (Sum.inl r))).val < 2 := by
    have hs := supported_at family (a, h) (halving.position (Sum.inl r))
    rcases hs with ⟨_, hy, _⟩ | ⟨_, hy, _⟩ | ⟨_, hy, _⟩ | ⟨_, hy, _⟩ <;>
      simp [hy]
  let word (h : Fin H) (r : Fin N) : Fin 2 :=
    ⟨((family.entry (a, h)).val 1 (halving.position (Sum.inl r))).val, y_binary h r⟩
  let code (h : Fin H) : Fin k × (Fin N → Fin 2) := (coloring (a, h), word h)
  have hinj : Function.Injective code := by
    intro h j heq
    have hcolor : coloring (a, h) = coloring (a, j) := congrArg Prod.fst heq
    have hword : word h = word j := congrArg Prod.snd heq
    have hs : family.PairedCyclicSupported halving (a, h) (a, j) (a, j) := by
      constructor
      · intro r
        have hyr : (family.entry (a, h)).val 1 (halving.position (Sum.inl r)) =
            (family.entry (a, j)).val 1 (halving.position (Sum.inl r)) :=
          Fin.ext (congrArg (fun v : Fin 2 => v.val) (congrFun hword r))
        rw [hyr]
        exact supported_at family (a, j) _
      · intro r
        rw [family.zSameFiber a h j]
        exact supported_at family (a, j) _
    by_contra hne
    apply coloring.valid (show (family.pairedCyclicConflictGraph halving).Adj (a, h) (a, j)
      from ?_) hcolor
    refine ⟨fun hpq => hne (congrArg Prod.snd hpq), Or.inl ?_⟩
    refine ⟨(a, h), (a, j), (a, j), hs, ?_, Or.inl rfl, Or.inr (Or.inl rfl)⟩
    exact fun hpq => hne (congrArg Prod.snd hpq.1)
  simpa [code] using Fintype.card_le_of_injective code hinj

private theorem first_y_balanced
    {N L G A H : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (p : Fin A × Fin H) :
    (Finset.univ.filter (fun r : Fin N =>
      (family.entry p).val 1 (halving.position (Sum.inl r)) = 1)).card = halving.half := by
  classical
  have htotal : (Finset.univ.filter (fun j : Fin (2 * N) =>
      (family.entry p).val 1 j = 1)).card = N := by
    simpa [cwQ6CoupledMarginalMultiplicity] using (family.entry p).property.2 1 1
  have hsum := halving.position.sum_comp
    (fun j => if (family.entry p).val 1 j = 1 then (1 : ℕ) else 0)
  rw [Fintype.sum_sum_type] at hsum
  simp only [← Finset.card_filter] at hsum
  have hright := halving.second_y p 1
  simp only [Fintype.card_subtype, Fin.isValue, one_ne_zero, ↓reduceIte] at hright
  have heven := halving.even_length
  omega

/-- Balance sharpens the binary-word bound to the number of half-size
subsets of the N positions. -/
theorem solution
    {N L G A H k : ℕ} (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (hA : 0 < A)
    (coloring : (family.pairedCyclicConflictGraph halving).Coloring (Fin k)) :
    H ≤ k * N.choose halving.half := by
  classical
  let a : Fin A := ⟨0, hA⟩
  let subsets := (Finset.univ : Finset (Fin N)).powersetCard halving.half
  let ones (h : Fin H) : subsets :=
    ⟨Finset.univ.filter (fun r : Fin N =>
      (family.entry (a, h)).val 1 (halving.position (Sum.inl r)) = 1),
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,
        first_y_balanced family halving (a, h)⟩⟩
  let code (h : Fin H) : Fin k × subsets := (coloring (a, h), ones h)
  have hinj : Function.Injective code := by
    intro h j heq
    have hcolor : coloring (a, h) = coloring (a, j) := congrArg Prod.fst heq
    have hones : (ones h).val = (ones j).val := congrArg Subtype.val (congrArg Prod.snd heq)
    have hy (r : Fin N) :
        (family.entry (a, h)).val 1 (halving.position (Sum.inl r)) =
        (family.entry (a, j)).val 1 (halving.position (Sum.inl r)) := by
      have hmem := Finset.ext_iff.mp hones r
      simp only [ones, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
      have hs := supported_at family (a, h) (halving.position (Sum.inl r))
      have ht := supported_at family (a, j) (halving.position (Sum.inl r))
      rcases hs with ⟨_, hy, _⟩ | ⟨_, hy, _⟩ | ⟨_, hy, _⟩ | ⟨_, hy, _⟩ <;>
        rcases ht with ⟨_, jy, _⟩ | ⟨_, jy, _⟩ | ⟨_, jy, _⟩ | ⟨_, jy, _⟩ <;>
        simp_all
    have hs : family.PairedCyclicSupported halving (a, h) (a, j) (a, j) := by
      constructor
      · intro r
        rw [hy r]
        exact supported_at family (a, j) _
      · intro r
        rw [family.zSameFiber a h j]
        exact supported_at family (a, j) _
    by_contra hne
    apply coloring.valid (show (family.pairedCyclicConflictGraph halving).Adj (a, h) (a, j)
      from ?_) hcolor
    refine ⟨fun hpq => hne (congrArg Prod.snd hpq), Or.inl ?_⟩
    refine ⟨(a, h), (a, j), (a, j), hs, ?_, Or.inl rfl, Or.inr (Or.inl rfl)⟩
    exact fun hpq => hne (congrArg Prod.snd hpq.1)
  simpa [subsets, Finset.card_powersetCard] using Fintype.card_le_of_injective code hinj

