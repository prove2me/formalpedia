-- Prove2me | solution 1 for RybinAI2026.P20.one_column_separation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T00:16:06.531293+00:00
-- url     : https://prove2.me/submissions/d47ae1a7-9107-4536-9799-1a60366fc7e2

/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Copyright (c) 2024 Thomas Browning. All rights reserved.
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning, Junyan Xu, Aristotle AI

Selected parity and nonsingularity lemmas from Mathlib revision
0df444a360eaa60ab8c11dca51a86af692955474, ported to Lean 4.30.
-/

import Mathlib.LinearAlgebra.Matrix.SemiringInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.GroupTheory.Perm.Option
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.CongrExclamation

namespace Equiv.Perm

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

@[simp] theorem sign_trans_trans (f : β ≃ α) (p : Perm α) (g : α ≃ β) :
    sign (f.trans (p.trans g)) = sign p * sign (f.trans g) := by
  rw [← sign_permCongr g, ← sign_mul]; congr; ext; simp

@[simp] theorem sign_equivCongr (f g : α ≃ β) (p : Perm α) :
    sign (f.equivCongr g p) = sign p * sign (f.symm.trans g) :=
  sign_trans_trans ..

end Equiv.Perm

open Equiv Equiv.Perm Finset

namespace Matrix

variable {n m R : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CommSemiring R]
variable (s : ℤˣ) (A : Matrix n n R)

@[simp] lemma detp_transpose : A.transpose.detp s = A.detp s :=
  sum_equiv (.inv _) (by simp) fun σ _ ↦ prod_equiv σ (by simp) (by simp)

@[simp] lemma detp_one_of_isEmpty [IsEmpty n] : A.detp 1 = 1 := by
  rw [detp, sum_unique_nonempty _ _ ⟨1, _⟩] <;> simp

@[simp] lemma detp_neg_one_of_isEmpty [IsEmpty n] : A.detp (-1) = 0 := by
  rw [detp, ofSign, univ_unique]
  convert sum_empty
  simp +decide

@[simp] lemma detp_submatrix_equiv_equiv (f g : m ≃ n) :
    (A.submatrix f g).detp s = A.detp (s * sign (f.symm.trans g)) :=
  sum_equiv (equivCongr f g) (by simp) fun _ _ ↦ prod_equiv f (by simp) fun _ _ ↦ by simp

def IsDetpBalanced (a b : R) : Prop :=
  a * A.detp 1 + b * A.detp (-1) = b * A.detp 1 + a * A.detp (-1)

variable {A} {a b : R}

lemma IsDetpBalanced.of_eq (eq : A.detp 1 = A.detp (-1)) : A.IsDetpBalanced a b := by
  rw [IsDetpBalanced, eq, add_comm]

lemma IsDetpBalanced.mul_add_mul_eq (h : A.IsDetpBalanced a b) (s t : ℤˣ) :
    a * A.detp s + b * A.detp t = b * A.detp s + a * A.detp t := by
  obtain rfl | rfl := Int.units_eq_one_or s <;> obtain rfl | rfl := Int.units_eq_one_or t
  · rw [add_comm]
  · rw [h]
  · rw [add_comm, ← h, add_comm]
  · rw [add_comm]

@[simp] lemma isDetpBalanced_transpose_iff : Aᵀ.IsDetpBalanced a b ↔ A.IsDetpBalanced a b := by
  simp [IsDetpBalanced]

lemma IsDetpBalanced.submatrix_equiv (e₁ e₂ : m ≃ n) (h : A.IsDetpBalanced a b) :
    (A.submatrix e₁ e₂).IsDetpBalanced a b := by
  simp_rw [IsDetpBalanced, detp_submatrix_equiv_equiv]
  apply h.mul_add_mul_eq

@[simp] lemma isDetpBalanced_submatrix_equiv_iff {e₁ e₂ : m ≃ n} :
    (A.submatrix e₁ e₂).IsDetpBalanced a b ↔ A.IsDetpBalanced a b where
  mp h := by simpa using h.submatrix_equiv e₁.symm e₂.symm
  mpr := (·.submatrix_equiv ..)

variable (A) in
def Nonsingular : Prop := ∀ a b : R, A.IsDetpBalanced a b → a = b

@[simp] lemma nonsingular_transpose_iff : Aᵀ.Nonsingular ↔ A.Nonsingular := by
  simp [Nonsingular]

lemma detp_eq_of_row_eq {p q : n} (hpq : p ≠ q) (hrow : A.row p = A.row q)
    (s : ℤˣ := 1) (t : ℤˣ := -1) : A.detp s = A.detp t := by
  have : A.detp 1 = A.detp (-1) := sum_equiv (.mulRight <| swap p q) (by simp [hpq])
    fun _ _ ↦ prod_equiv (swap p q) (by simp) (by aesop (add simp row))
  obtain rfl | rfl := Int.units_eq_one_or s <;>
  obtain rfl | rfl := Int.units_eq_one_or t <;>
  first | rfl | rw [this]

lemma detp_eq_of_col_eq {p q : n} (hpq : p ≠ q) (hcol : A.col p = A.col q)
    (s : ℤˣ := 1) (t : ℤˣ := -1) : A.detp s = A.detp t := by
  simpa using detp_eq_of_row_eq (A := Aᵀ) hpq hcol s t

lemma IsDetpBalanced.submatrix_of_card_le (h : A.IsDetpBalanced a b)
    (le : Fintype.card n ≤ Fintype.card m) (f g : m → n) :
    (A.submatrix f g).IsDetpBalanced a b := by
  by_cases hf : f.Injective; swap
  · obtain ⟨p, q, eq, ne⟩ := Function.not_injective_iff.mp hf
    exact .of_eq (detp_eq_of_row_eq ne <| by ext; simp [eq])
  by_cases hg : g.Injective; swap
  · obtain ⟨p, q, eq, ne⟩ := Function.not_injective_iff.mp hg
    exact .of_eq (detp_eq_of_col_eq ne <| by ext; simp [eq])
  let f' := Equiv.ofBijective f <| (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hf, (Fintype.card_le_of_injective f hf).antisymm le⟩
  let g' := Equiv.ofBijective g <| (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hg, (Fintype.card_le_of_injective g hg).antisymm le⟩
  rwa [show f = f' by rfl, show g = g' by rfl, isDetpBalanced_submatrix_equiv_iff]

private lemma adjp_none_right (A : Matrix (Option n) (Option n) R) (i : Option n) :
    A.adjp s i none = (A.submatrix some <| swap none i ∘ some).detp (sign (swap none i) * s) := by
  rw [adjp, of_apply, detp]
  convert sum_image (g := fun σ ↦ decomposeOption.symm (i, σ))
    ((Equiv.injective _).comp (Prod.mk_right_injective i)).injOn
  · ext σ; simp only [mem_filter, mem_ofSign, mem_image]
    exact ⟨fun _ ↦ ⟨σ.removeNone, by rw [← optionCongr_sign]; aesop⟩, by aesop⟩
  convert (prod_image (Option.some_injective n).injOn).symm
  · rfl
  · apply SetLike.coe_injective; simp [← Set.compl_range_some]

lemma adjp_none_none (A : Matrix (Option n) (Option n) R) :
    A.adjp s none none = (A.submatrix some some).detp s := by
  simp [adjp_none_right]

lemma adjp_some_none (A : Matrix (Option n) (Option n) R) (i : n) :
    A.adjp s (some i) none = (A.submatrix some (Function.update some i none)).detp (-s) := by
  rw [adjp_none_right]; congr
  · simp
  · ext1; aesop

lemma detp_option_expand_row_none (A : Matrix (Option n) (Option n) R) :
    A.detp s = A none none * (A.submatrix some some).detp s +
      ∑ k : n, A none (some k) * (A.submatrix some (Function.update some k none)).detp (-s) := by
  simp_rw [← A.mul_adjp_apply_eq s none, mul_apply,
    Fintype.sum_option, adjp_none_none, adjp_some_none]

theorem Nonsingular.of_linearIndependent_col (ind : LinearIndependent R A.col) : A.Nonsingular := by
  intro a b bal
  let P (r : ℕ) : Prop := ∀ f g : Fin r → n, (A.submatrix f g).IsDetpBalanced a b
  suffices h : P 0 by simpa [IsDetpBalanced] using h Fin.elim0 Fin.elim0
  refine Nat.decreasingInduction' (n := Fintype.card n) (fun r _ _ ih f g ↦ ?_) (Nat.zero_le _) <|
    bal.submatrix_of_card_le (Fintype.card_fin _).ge
  by_cases hg : g.Surjective
  · exact bal.submatrix_of_card_le (Fintype.card_le_of_surjective g hg) f g
  obtain ⟨j₀, h₀⟩ := by simpa [Function.Surjective] using hg
  let D := A.submatrix f g
  let Aj (j : Fin r) := A.submatrix f (Function.update g j j₀)
  let v (a b : R) : n →₀ R := ∑ j, .single (g j) (a * (Aj j).detp (-1) + b * (Aj j).detp 1) +
    .single j₀ (a * D.detp 1 + b * D.detp (-1))
  suffices h : v a b = v b a by simpa [IsDetpBalanced, v, h₀] using congr($h j₀)
  refine ind (funext fun i ↦ ?_)
  let Ai := A.submatrix (Option.rec i f) (Option.rec j₀ g)
  have (s : ℤˣ) : Ai.detp s = ∑ j, (Aj j).detp (-s) * A.col (g j) i + D.detp s * A.col j₀ i := by
    simp_rw [mul_comm]; rw [detp_option_expand_row_none, add_comm]
    congr!; aesop (add simp Function.update)
  have (a b : R) : (v a b).linearCombination R A.col i = a * Ai.detp 1 + b * Ai.detp (-1) := by
    simp [v, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, add_add_add_comm, mul_add, this]
  simpa [this, IsDetpBalanced, ← submatrix_submatrix] using
    ih (Option.rec i f ∘ finSuccEquiv r) (Option.rec j₀ g ∘ finSuccEquiv r)

theorem Nonsingular.of_linearIndependent_row (ind : LinearIndependent R A.row) : A.Nonsingular := by
  simpa using Nonsingular.of_linearIndependent_col (A := Aᵀ) ind

end Matrix

namespace TransposeColumnSeparation

theorem detp_mul_eq_of_column_mul_eq
    {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (q : Fin n) (r s : R)
    (hcol : ∀ i, A i q * r = A i q * s) (t : ℤˣ) :
    A.detp t * r = A.detp t * s := by
  classical
  simp only [Matrix.detp, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [← Finset.mul_prod_erase Finset.univ (fun i => A i (σ i))
    (Finset.mem_univ (σ.symm q))]
  simp only [Equiv.apply_symm_apply]
  calc
    (A (σ.symm q) q * ∏ i ∈ Finset.univ.erase (σ.symm q), A i (σ i)) * r =
        (A (σ.symm q) q * r) * ∏ i ∈ Finset.univ.erase (σ.symm q), A i (σ i) := by
      ac_rfl
    _ = (A (σ.symm q) q * s) * ∏ i ∈ Finset.univ.erase (σ.symm q), A i (σ i) := by
      rw [hcol]
    _ = (A (σ.symm q) q * ∏ i ∈ Finset.univ.erase (σ.symm q), A i (σ i)) * s := by
      ac_rfl

theorem column_separation
    {R : Type*} [CommSemiring R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R)
    (hA : Function.Injective A.transpose.mulVec)
    (q : Fin n) (r s : R)
    (hcol : ∀ i, A i q * r = A i q * s) : r = s := by
  have hns : A.Nonsingular :=
    Matrix.Nonsingular.of_linearIndependent_row (Matrix.mulVec_injective_iff.mp hA)
  have hd (t : ℤˣ) : r * A.detp t = s * A.detp t := by
    simpa only [mul_comm] using detp_mul_eq_of_column_mul_eq A q r s hcol t
  apply hns r s
  change r * A.detp 1 + s * A.detp (-1) = s * A.detp 1 + r * A.detp (-1)
  rw [hd 1, hd (-1)]

end TransposeColumnSeparation

theorem solution
    {R : Type*} [CommSemiring R] {n : ℕ} (_hn : 2 ≤ n)
    (A : Matrix (Fin n) (Fin n) R)
    (hA : Function.Injective A.transpose.mulVec)
    (q : Fin n) (r s : R)
    (hcol : ∀ i, A i q * r = A i q * s) : r = s := by
  exact TransposeColumnSeparation.column_separation A hA q r s hcol
