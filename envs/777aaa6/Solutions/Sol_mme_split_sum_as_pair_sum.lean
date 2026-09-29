-- Prove2me | solution 1 for mme_split_sum_as_pair_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T18:54:50.621309+00:00
-- url     : https://prove2.me/submissions/ca9d9364-eae6-48b7-aeda-ba2797a1bd07

import Mathlib
import Definitions.Def_mme_recursive_thin_split_data
open BigOperators MME
open scoped Classical
set_option autoImplicit false


open BigOperators MME
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MME.SplitSum

/-- Admissible splits are exactly the admissible pairs of first grades. -/
def splitEquiv (half : ℕ) (par : Fin 3 → ℕ) :
    RecursiveThinSplit.Split half par ≃
      {p : Fin (half + 1) × Fin (half + 1) //
        p.1.val + p.2.val ≤ half ∧ p.1.val ≤ par 0 ∧ p.2.val ≤ par 1 ∧
          half - p.1.val - p.2.val ≤ par 2} where
  toFun x := ⟨(x.val 0, x.val 1), by
    obtain ⟨hsum, hle⟩ := x.property
    have h0 := hle 0
    have h1 := hle 1
    have h2 := hle 2
    exact ⟨by dsimp only; omega, h0, h1, by dsimp only; omega⟩⟩
  invFun p := ⟨![p.val.1, p.val.2, ⟨half - p.val.1.val - p.val.2.val, by
      have := p.val.1.isLt; omega⟩], by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    obtain ⟨hp1, hp2, hp3, hp4⟩ := p.property
    omega, by
    intro i
    obtain ⟨hp1, hp2, hp3, hp4⟩ := p.property
    match i with
    | 0 => simpa using hp2
    | 1 => simpa using hp3
    | 2 => simpa using hp4⟩
  left_inv x := by
    have h := x.property.1
    apply Subtype.ext
    funext i
    match i with
    | 0 => simp
    | 1 => simp
    | 2 => apply Fin.ext; simp; omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> simp

/-- A sum over admissible splits, as a double sum over the first two grades: summands that are
not admissible triples vanish. -/
theorem sum_split {half : ℕ} {par : Fin 3 → ℕ} {M : Type*} [AddCommMonoid M]
    (g : ℕ → ℕ → ℕ → M)
    (hg : ∀ a b c : ℕ, ¬ (a + b + c = half ∧ a ≤ par 0 ∧ b ≤ par 1 ∧ c ≤ par 2) → g a b c = 0) :
    ∑ x : RecursiveThinSplit.Split half par, g (x.val 0).val (x.val 1).val (x.val 2).val =
      ∑ a : Fin (half + 1), ∑ b : Fin (half + 1), g a.val b.val (half - a.val - b.val) := by
  classical
  have hsub : ∑ x : RecursiveThinSplit.Split half par, g (x.val 0).val (x.val 1).val (x.val 2).val =
      ∑ q : {p : Fin (half + 1) × Fin (half + 1) //
          p.1.val + p.2.val ≤ half ∧ p.1.val ≤ par 0 ∧ p.2.val ≤ par 1 ∧
            half - p.1.val - p.2.val ≤ par 2},
        g q.val.1.val q.val.2.val (half - q.val.1.val - q.val.2.val) := by
    refine Fintype.sum_equiv (splitEquiv half par) _ _ (fun x ↦ ?_)
    have h := x.property.1
    have h2 : (x.val 2).val = half - (x.val 0).val - (x.val 1).val := by omega
    rw [h2]
    rfl
  rw [hsub, ← Fintype.sum_prod_type',
    ← Finset.sum_subtype (p := fun p : Fin (half + 1) × Fin (half + 1) ↦
        p.1.val + p.2.val ≤ half ∧ p.1.val ≤ par 0 ∧ p.2.val ≤ par 1 ∧
          half - p.1.val - p.2.val ≤ par 2)
      (s := (Finset.univ : Finset (Fin (half + 1) × Fin (half + 1))).filter
        (fun p ↦ p.1.val + p.2.val ≤ half ∧ p.1.val ≤ par 0 ∧ p.2.val ≤ par 1 ∧
          half - p.1.val - p.2.val ≤ par 2)) (by intro p; simp)
      (f := fun p ↦ g p.1.val p.2.val (half - p.1.val - p.2.val))]
  refine Finset.sum_filter_of_ne (fun p _ hne ↦ ?_)
  by_contra hc
  exact hne (hg _ _ _ (by
    intro hv
    exact hc ⟨by omega, hv.2.1, hv.2.2.1, hv.2.2.2⟩))

end MME.SplitSum


open MME.SplitSum in
theorem solution {half : ℕ} {par : Fin 3 → ℕ} {M : Type*} [AddCommMonoid M]
    (g : ℕ → ℕ → ℕ → M)
    (hg : ∀ a b c : ℕ, ¬ (a + b + c = half ∧ a ≤ par 0 ∧ b ≤ par 1 ∧ c ≤ par 2) → g a b c = 0) :
    ∑ x : RecursiveThinSplit.Split half par, g (x.val 0).val (x.val 1).val (x.val 2).val =
      ∑ a : Fin (half + 1), ∑ b : Fin (half + 1), g a.val b.val (half - a.val - b.val) :=
  MME.SplitSum.sum_split g hg
