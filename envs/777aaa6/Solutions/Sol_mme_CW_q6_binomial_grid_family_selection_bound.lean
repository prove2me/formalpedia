-- Prove2me | solution 1 for mme_CW_q6_binomial_grid_family_selection_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T02:07:31.993905+00:00
-- url     : https://prove2.me/submissions/b223f4a1-372c-425a-82dc-b5b89395a7ef

import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FinCases
import Mathlib.Data.Finset.Powerset

open MME BigOperators

namespace MME.BalancedGrid

variable {N B half : ℕ}

def position (N : ℕ) : (Fin N ⊕ Fin N) ≃ Fin (2 * N) :=
  finSumFinEquiv.trans (finCongr (by omega))

def bit (b : Fin 2) : Fin 3 := ⟨b.val, by omega⟩
def opposite (b : Fin 2) : Fin 3 := if b = 0 then 1 else 0

def fullWord (word : Fin B → Fin N → Fin 2) (h : Fin (B * B))
    (j : Fin (2 * N)) : Fin 2 :=
  Sum.elim (word (finProdFinEquiv.symm h).1)
    (word (finProdFinEquiv.symm h).2) ((position N).symm j)

def raw (word : Fin B → Fin N → Fin 2) (h : Fin (B * B)) :
    CWQ6CoupledAddress N :=
  ![fun j ↦ bit (fullWord word h j), fun j ↦ opposite (fullWord word h j), fun _ ↦ 2]

private theorem bit_supported (b : Fin 2) :
    CWQ6CoupledLocalSupported (bit b) (opposite b) 2 := by
  fin_cases b <;> simp [CWQ6CoupledLocalSupported, bit, opposite]

private theorem bit_injective : Function.Injective bit := by
  intro a b h
  exact Fin.ext (congrArg (fun v : Fin 3 ↦ v.val) h)

private theorem opposite_injective : Function.Injective opposite := by decide

private theorem half_bit_count (word : Fin B → Fin N → Fin 2)
    (hc : ∀ a b, (Finset.univ.filter (fun j ↦ word a j = b)).card = half)
    (a : Fin B) (r : Fin 3) :
    (∑ j : Fin N, if bit (word a j) = r then 1 else 0) =
      if r = 0 then half else if r = 1 then half else 0 := by
  have hb (v : Fin 2) : bit v = 0 ↔ v = 0 := by fin_cases v <;> decide
  have ho (v : Fin 2) : bit v = 1 ↔ v = 1 := by fin_cases v <;> decide
  have ht (v : Fin 2) : bit v ≠ 2 := by fin_cases v <;> decide
  fin_cases r
  · simpa [hb, ← Finset.card_filter] using hc a 0
  · simpa [ho, ← Finset.card_filter] using hc a 1
  · simp [ht]

private theorem half_opposite_count (word : Fin B → Fin N → Fin 2)
    (hc : ∀ a b, (Finset.univ.filter (fun j ↦ word a j = b)).card = half)
    (a : Fin B) (r : Fin 3) :
    (∑ j : Fin N, if opposite (word a j) = r then 1 else 0) =
      if r = 0 then half else if r = 1 then half else 0 := by
  have hb (v : Fin 2) : opposite v = 0 ↔ v = 1 := by fin_cases v <;> decide
  have ho (v : Fin 2) : opposite v = 1 ↔ v = 0 := by fin_cases v <;> decide
  have ht (v : Fin 2) : opposite v ≠ 2 := by fin_cases v <;> decide
  fin_cases r
  · simpa [hb, ← Finset.card_filter] using hc a 1
  · simpa [ho, ← Finset.card_filter] using hc a 0
  · simp [ht]

private theorem full_count (f : Fin 2 → Fin 3) (word : Fin B → Fin N → Fin 2)
    (hc : ∀ a r, (∑ j : Fin N, if f (word a j) = r then 1 else 0) =
      if r = 0 then half else if r = 1 then half else 0)
    (heven : N = 2 * half) (h : Fin (B * B)) (r : Fin 3) :
    (Finset.univ.filter (fun j ↦ f (fullWord word h j) = r)).card =
      if r = 0 then N else if r = 1 then N else 0 := by
  have hs := (position N).sum_comp (fun j ↦ if f (fullWord word h j) = r then (1 : ℕ) else 0)
  rw [Fintype.sum_sum_type] at hs
  simp only [fullWord, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] at hs
  rw [hc, hc] at hs
  rw [Finset.card_filter]
  fin_cases r <;> simpa only [Fin.reduceFinMk, Fin.isValue, ite_true, ite_false,
    zero_ne_one, one_ne_zero, heven, two_mul, fullWord] using hs.symm

def address (word : Fin B → Fin N → Fin 2)
    (hc : ∀ a b, (Finset.univ.filter (fun j ↦ word a j = b)).card = half)
    (heven : N = 2 * half) (h : Fin (B * B)) : CWQ6ExactCoupledAddress N 0 N :=
  ⟨raw word h, by
    constructor
    · intro j
      exact bit_supported (fullWord word h j)
    · intro i r
      fin_cases i
      · exact full_count bit word (half_bit_count word hc) heven h r
      · exact full_count opposite word (half_opposite_count word hc) heven h r
      · change (Finset.univ.filter (fun _ : Fin (2 * N) ↦ (2 : Fin 3) = r)).card =
          if r = 0 then 0 else if r = 1 then 0 else 2 * N
        fin_cases r <;> simp⟩

private theorem fullWord_injective (word : Fin B → Fin N → Fin 2)
    (hinj : Function.Injective word) : Function.Injective (fullWord word) := by
  intro h k heq
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · apply hinj
    funext j
    have hj := congrFun heq (position N (Sum.inl j))
    simpa only [fullWord, Equiv.symm_apply_apply, Sum.elim_inl] using hj
  · apply hinj
    funext j
    have hj := congrFun heq (position N (Sum.inr j))
    simpa only [fullWord, Equiv.symm_apply_apply, Sum.elim_inr] using hj

def family (word : Fin B → Fin N → Fin 2)
    (hc : ∀ a b, (Finset.univ.filter (fun j ↦ word a j = b)).card = half)
    (heven : N = 2 * half) (hinj : Function.Injective word) (hB : 0 < B) :
    CWQ6PrimaryHashFamily N 0 N 1 (B * B) where
  hHpos := Nat.mul_pos hB hB
  entry p := address word hc heven p.2
  xInjective := by
    intro p q heq
    apply Prod.ext (Subsingleton.elim _ _)
    apply fullWord_injective word hinj
    funext j
    exact bit_injective (congrFun heq j)
  yInjective := by
    intro p q heq
    apply Prod.ext (Subsingleton.elim _ _)
    apply fullWord_injective word hinj
    funext j
    exact opposite_injective (congrFun heq j)
  zSameFiber := by intros; rfl
  zSeparatesFibers := by intros; exact Subsingleton.elim _ _
  induced := by
    intro p q r hs
    refine ⟨?_, Subsingleton.elim _ _⟩
    apply Prod.ext (Subsingleton.elim _ _)
    apply fullWord_injective word hinj
    funext j
    have h := hs j
    change CWQ6CoupledLocalSupported (bit (fullWord word p.2 j))
      (opposite (fullWord word q.2 j)) 2 at h
    have mixed (a b : Fin 2) :
        CWQ6CoupledLocalSupported (bit a) (opposite b) 2 → a = b := by
      fin_cases a <;> fin_cases b <;> simp [CWQ6CoupledLocalSupported, bit, opposite]
    exact mixed _ _ h

def halving (word : Fin B → Fin N → Fin 2)
    (hc : ∀ a b, (Finset.univ.filter (fun j ↦ word a j = b)).card = half)
    (heven : N = 2 * half) (hinj : Function.Injective word) (hB : 0 < B) :
    (family word hc heven hinj hB).CommonBalancedXYHalving where
  half := half
  even_length := heven
  position := position N
  first_x := by
    intro p r
    change Fintype.card {j : Fin N // bit (fullWord word p.2 (position N (Sum.inl j))) = r} = _
    simp only [fullWord, Equiv.symm_apply_apply, Sum.elim_inl, Fintype.card_subtype]
    simp only [Finset.card_filter]
    exact half_bit_count word hc _ r
  second_y := by
    intro p r
    change Fintype.card {j : Fin N // opposite (fullWord word p.2 (position N (Sum.inr j))) = r} = _
    simp only [fullWord, Equiv.symm_apply_apply, Sum.elim_inr, Fintype.card_subtype]
    simp only [Finset.card_filter]
    exact half_opposite_count word hc _ r

/-- A selected diagonal can use each left word only once. -/
theorem selected_card_le (word : Fin B → Fin N → Fin 2)
    (hc : ∀ a b, (Finset.univ.filter (fun j ↦ word a j = b)).card = half)
    (heven : N = 2 * half) (hinj : Function.Injective word) (hB : 0 < B)
    (q : ℕ) (index : Fin q → Fin 1 × Fin (B * B))
    (hselected : ∀ i j k,
      (family word hc heven hinj hB).PairedCyclicSupported
        (halving word hc heven hinj hB) (index i) (index j) (index k) →
      i = j ∧ j = k) : q ≤ B := by
  let row (i : Fin q) : Fin B := (finProdFinEquiv.symm (index i).2).1
  have hr : Function.Injective row := by
    intro i j heq
    apply (hselected i j j ?_).1
    constructor
    · intro r
      change CWQ6CoupledLocalSupported
        (bit (fullWord word (index j).2 (position N (Sum.inl r))))
        (opposite (fullWord word (index i).2 (position N (Sum.inl r)))) 2
      simp only [fullWord, Equiv.symm_apply_apply, Sum.elim_inl]
      change CWQ6CoupledLocalSupported (bit (word (row j) r))
        (opposite (word (row i) r)) 2
      rw [heq]
      exact bit_supported _
    · intro r
      exact bit_supported (fullWord word (index j).2 (position N (Sum.inr r)))
  simpa using Fintype.card_le_of_injective row hr

end MME.BalancedGrid


/-- Independently pairing balanced binary words gives a primary family whose
paired-induced selections have only square-root size. -/
theorem mme_CW_q6_balanced_word_grid_family_selection_bound
    {N B half : ℕ} (word : Fin B → Fin N → Fin 2)
    (hc : ∀ a b, (Finset.univ.filter (fun j ↦ word a j = b)).card = half)
    (heven : N = 2 * half) (hinj : Function.Injective word) (hB : 0 < B) :
    ∃ family : CWQ6PrimaryHashFamily N 0 N 1 (B * B),
      ∃ halving : family.CommonBalancedXYHalving,
        ∀ (q : ℕ) (index : Fin q → Fin 1 × Fin (B * B)),
          (∀ i j k, family.PairedCyclicSupported halving (index i) (index j) (index k) →
            i = j ∧ j = k) → q ≤ B := by
  exact ⟨MME.BalancedGrid.family word hc heven hinj hB,
    MME.BalancedGrid.halving word hc heven hinj hB,
    MME.BalancedGrid.selected_card_le word hc heven hinj hB⟩


/-- The complete balanced-word grid has binomial-square many entries, but
every paired-induced selection has at most one binomial factor. -/
theorem solution (n : ℕ) :
    ∃ family : CWQ6PrimaryHashFamily (2 * n) 0 (2 * n) 1
        ((2 * n).choose n * (2 * n).choose n),
      ∃ halving : family.CommonBalancedXYHalving,
        ∀ (q : ℕ) (index : Fin q → Fin 1 ×
            Fin ((2 * n).choose n * (2 * n).choose n)),
          (∀ i j k, family.PairedCyclicSupported halving (index i) (index j) (index k) →
            i = j ∧ j = k) → q ≤ (2 * n).choose n := by
  classical
  let subsets := (Finset.univ : Finset (Fin (2 * n))).powersetCard n
  let e : subsets ≃ Fin ((2 * n).choose n) :=
    Fintype.equivFinOfCardEq (by simp [subsets])
  let word (a : Fin ((2 * n).choose n)) (j : Fin (2 * n)) : Fin 2 :=
    if j ∈ (e.symm a).val then 0 else 1
  have hc (a : Fin ((2 * n).choose n)) (b : Fin 2) :
      (Finset.univ.filter (fun j ↦ word a j = b)).card = n := by
    have hcard : (e.symm a).val.card = n :=
      (Finset.mem_powersetCard.mp (e.symm a).property).2
    have hz : Finset.univ.filter (fun j ↦ word a j = 0) = (e.symm a).val := by
      ext j
      simp [word]
    have ho : Finset.univ.filter (fun j ↦ word a j = 1) =
        Finset.univ \ (e.symm a).val := by
      ext j
      simp [word]
    fin_cases b
    · change (Finset.univ.filter (fun j ↦ word a j = 0)).card = n
      rw [hz]
      exact hcard
    · change (Finset.univ.filter (fun j ↦ word a j = 1)).card = n
      rw [ho, Finset.card_sdiff]
      simp [hcard, two_mul]
  have hinj : Function.Injective word := by
    intro a b h
    apply e.symm.injective
    apply Subtype.ext
    ext j
    have hh : (word a j = 0) ↔ (word b j = 0) := by rw [h]
    simpa [word] using hh
  exact mme_CW_q6_balanced_word_grid_family_selection_bound word hc rfl hinj
    (Nat.choose_pos (by omega))

