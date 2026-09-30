-- Prove2me | solution 1 for RybinAI2026.P20.summand_separation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T00:30:12.062017+00:00
-- url     : https://prove2.me/submissions/a19b8fe4-46fb-4a4b-afe8-ae8933151bc1

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

namespace TransposeSummandSeparation

open Finset Equiv Equiv.Perm

variable {R : Type*} [CommSemiring R]
variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

lemma detp_option_expand_col_none (A : Matrix (Option m) (Option m) R) (s : ℤˣ) :
    A.detp s = A none none * (A.submatrix some some).detp s +
      ∑ k : m, A (some k) none *
        (A.submatrix (Function.update some k none) some).detp (-s) := by
  simpa only [← Matrix.transpose_submatrix, Matrix.detp_transpose, Matrix.transpose_apply]
    using Matrix.detp_option_expand_row_none s A.transpose

def minor (A : Matrix n n R) (f : Option m → n) (g : m → n) (j : n) :
    Matrix (Option m) (Option m) R :=
  A.submatrix f (Option.rec j g)

def weighted (A : Matrix n n R) (f : Option m → n) (g : m → n)
    (q : n) (s : ℤˣ) (v : n → R) : R :=
  ∑ j, (minor A f g j).detp (if j = q then -s else s) * v j

lemma ordinary_eq (A : Matrix n n R) (f : Option m → n) (g : m → n)
    (s : ℤˣ) {x y : n → R} (hxy : A.mulVec x = A.mulVec y) :
    (∑ j, (minor A f g j).detp s * x j) =
      ∑ j, (minor A f g j).detp s * y j := by
  have hexp (j : n) :
      (minor A f g j).detp s =
        A (f none) j * (A.submatrix (f ∘ some) g).detp s +
        ∑ k : m, A (f (some k)) j *
          (A.submatrix (f ∘ Function.update some k none) g).detp (-s) := by
    simpa [minor, Matrix.submatrix_submatrix, Function.comp_def]
      using detp_option_expand_col_none (minor A f g j) s
  simp_rw [hexp, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [Finset.sum_comm (f := fun (j : n) (k : m) => A (f (some k)) j *
      (A.submatrix (f ∘ Function.update some k none) g).detp (-s) * x j),
    Finset.sum_comm (f := fun (j : n) (k : m) => A (f (some k)) j *
      (A.submatrix (f ∘ Function.update some k none) g).detp (-s) * y j)]
  have hrow (i : n) : ∑ j, A i j * x j = ∑ j, A i j * y j :=
    congrFun hxy i
  congr 1
  · simpa only [mul_right_comm, ← Finset.sum_mul] using
      congrArg (· * (A.submatrix (f ∘ some) g).detp s) (hrow (f none))
  · apply Finset.sum_congr rfl
    intro k hk
    simpa only [mul_right_comm, ← Finset.sum_mul] using
      congrArg (· * (A.submatrix (f ∘ Function.update some k none) g).detp (-s))
        (hrow (f (some k)))

lemma weighted_eq_ordinary_of_mem (A : Matrix n n R) (f : Option m → n)
    (g : m → n) (q : n) (s : ℤˣ) (v : n → R) (hq : ∃ k, g k = q) :
    weighted A f g q s v = ∑ j, (minor A f g j).detp s * v j := by
  obtain ⟨k, hk⟩ := hq
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j = q
  · subst j
    simp only [ite_true]
    congr 1
    exact Matrix.detp_eq_of_col_eq (A := minor A f g q)
      (p := none) (q := some k) (by simp)
      (by ext i; simp [minor, Matrix.col, hk]) (-s) s
  · simp [h]

lemma detp_submatrix_eq_of_not_injective (A : Matrix n n R) (f g : m → n)
    (hg : ¬ Function.Injective g) (s t : ℤˣ) :
    (A.submatrix f g).detp s = (A.submatrix f g).detp t := by
  obtain ⟨p, q, heq, hne⟩ := Function.not_injective_iff.mp hg
  exact Matrix.detp_eq_of_col_eq hne (by ext; simp [Matrix.col, heq]) s t

lemma double_swap (A : Matrix n n R) (f : Option (Option m) → n) (g : m → n)
    (j z : n) (s : ℤˣ) :
    (minor A f (Option.rec j g) z).detp s =
      (minor A f (Option.rec z g) j).detp (-s) := by
  have he : minor A f (Option.rec j g) z =
      (minor A f (Option.rec z g) j).submatrix (Equiv.refl _)
        (Equiv.swap none (some none)) := by
    ext a b
    rcases b with _ | (_ | b) <;>
      simp [minor, Matrix.submatrix, Equiv.swap_apply_def]
  rw [he, Matrix.detp_submatrix_equiv_equiv]
  simp

noncomputable def cofactorVector (A : Matrix n n R) (f : Option m → n) (g : m → n)
    (q τ : n) (s : ℤˣ) (v : n → R) : n →₀ R :=
  ∑ i, Finsupp.single (f i) (weighted A (Function.update f i τ) g q (-s) v) +
    Finsupp.single τ (weighted A f g q s v)

lemma cofactorVector_apply (A : Matrix n n R) (f : Option m → n) (g : m → n)
    (q τ : n) (s : ℤˣ) (v : n → R) (hτ : ∀ i, f i ≠ τ) :
    cofactorVector A f g q τ s v τ = weighted A f g q s v := by
  simp [cofactorVector, hτ]

lemma cofactorVector_linearCombination (A : Matrix n n R) (f : Option m → n)
    (g : m → n) (q τ : n) (s : ℤˣ) (v : n → R) (z : n) :
    (cofactorVector A f g q τ s v).linearCombination R A.row z =
      weighted A (Option.rec τ f) (Option.rec z g) q (-s) v := by
  have hexp (j : n) (t : ℤˣ) :
      (minor A (Option.rec τ f) (Option.rec j g) z).detp t =
        A τ z * (minor A f g j).detp t +
        ∑ i, A (f i) z * (minor A (Function.update f i τ) g j).detp (-t) := by
    rw [detp_option_expand_col_none]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    congr 1
    ext a b
    simp [minor, Matrix.submatrix, Function.update_apply]
    split_ifs <;> simp_all
  have hsign (j : n) : -(if j = q then -s else s) =
      if j = q then -(-s) else -s := by split <;> simp_all
  have hswap (j : n) :
      (minor A (Option.rec τ f) (Option.rec z g) j).detp
        (if j = q then -(-s) else -s) =
      (minor A (Option.rec τ f) (Option.rec j g) z).detp
        (if j = q then -s else s) := by
    rw [double_swap]
    split_ifs <;> simp
  simp only [weighted, hswap, hexp, hsign, add_mul, Finset.sum_add_distrib,
    Finset.sum_mul]
  simp only [cofactorVector, map_add, map_sum, Finsupp.linearCombination_single,
    Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm (f := fun (j : n) (i : Option m) => A (f i) z *
    (minor A (Function.update f i τ) g j).detp
      (if j = q then -(-s) else -s) * v j)]
  simp only [weighted, Finset.sum_mul, Matrix.row]
  ac_rfl

lemma descend (A : Matrix n n R) (hA : Function.Injective A.transpose.mulVec)
    (f : Option m → n) (g : m → n) (q τ : n) (s : ℤˣ) (x y : n → R)
    (hτ : ∀ i, f i ≠ τ)
    (ih : ∀ z, weighted A (Option.rec τ f) (Option.rec z g) q (-s) x =
      weighted A (Option.rec τ f) (Option.rec z g) q (-s) y) :
    weighted A f g q s x = weighted A f g q s y := by
  have ind : LinearIndependent R A.row := Matrix.mulVec_injective_iff.mp hA
  have huv : cofactorVector A f g q τ s x = cofactorVector A f g q τ s y := by
    apply ind
    ext z
    simpa only [cofactorVector_linearCombination] using ih z
  simpa only [cofactorVector_apply A f g q τ s x hτ,
    cofactorVector_apply A f g q τ s y hτ] using congrArg (· τ) huv

lemma weighted_single (A : Matrix n n R) (f : Option m → n) (g : m → n)
    (q z : n) (s : ℤˣ) :
    weighted A f g q s (Pi.single z 1) =
      (minor A f g z).detp (if z = q then -s else s) := by
  simp [weighted, Pi.single_apply, mul_ite]

lemma pairing_eq (A : Matrix n n R) (u : n →₀ R) {x y : n → R}
    (hxy : A.mulVec x = A.mulVec y) :
    (∑ j, u.linearCombination R A.row j * x j) =
      ∑ j, u.linearCombination R A.row j * y j := by
  have he (v : n → R) : (∑ j, u.linearCombination R A.row j * v j) =
      u.sum (fun i a => a * (A.mulVec v) i) := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, Matrix.row, Matrix.mulVec, dotProduct]
  rw [he, he, hxy]

lemma top_symmetric (A : Matrix n n R) (f : Option (Option m) → n) (g : m → n)
    (q : n) (s : ℤˣ) (hcard : Fintype.card (Option (Option m)) = Fintype.card n)
    (hq : ∀ i, g i ≠ q) (j z : n) :
    (minor A f (Option.rec z g) j).detp (if j = q then -s else s) =
      (minor A f (Option.rec j g) z).detp (if z = q then -s else s) := by
  rw [double_swap]
  by_cases hj : j = q <;> by_cases hz : z = q
  · subst j
    subst z
    simp only [ite_true, neg_neg]
    exact Matrix.detp_eq_of_col_eq (A := minor A f (Option.rec q g) q)
      (p := none) (q := some none) (by simp)
      (by ext i; simp [minor, Matrix.col]) s (-s)
  · simp [hj, hz]
  · simp [hj, hz]
  · simp only [hj, hz, ite_false]
    apply detp_submatrix_eq_of_not_injective
    intro hinj
    have hsurj : Function.Surjective (Option.rec z (Option.rec j g)) :=
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩).surjective
    obtain ⟨i, hi⟩ := hsurj q
    rcases i with _ | (_ | i) <;> simp_all

lemma top (A : Matrix n n R) (hA : Function.Injective A.transpose.mulVec)
    (f : Option m → n) (g : m → n) (q τ : n) (s : ℤˣ) (x y : n → R)
    (hxy : A.mulVec x = A.mulVec y)
    (hcard : Fintype.card (Option (Option m)) = Fintype.card n)
    (hτ : ∀ i, f i ≠ τ) :
    weighted A f g q s x = weighted A f g q s y := by
  by_cases hq : ∃ i, g i = q
  · rw [weighted_eq_ordinary_of_mem A f g q s x hq,
      weighted_eq_ordinary_of_mem A f g q s y hq]
    exact ordinary_eq A f g s hxy
  have hq' : ∀ i, g i ≠ q := by simpa using hq
  apply descend A hA f g q τ s x y hτ
  intro z
  let u := cofactorVector A f g q τ s (Pi.single z 1)
  have he (v : n → R) :
      weighted A (Option.rec τ f) (Option.rec z g) q (-s) v =
        ∑ j, u.linearCombination R A.row j * v j := by
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [cofactorVector_linearCombination, weighted_single]
    exact top_symmetric A (Option.rec τ f) g q (-s) hcard hq' j z
  rw [he, he]
  exact pairing_eq A u hxy

theorem summand_separation
    {N : ℕ} (hN : 2 ≤ N) (A : Matrix (Fin N) (Fin N) R)
    (hA : Function.Injective A.transpose.mulVec)
    (x y : Fin N → R) (hxy : A.mulVec x = A.mulVec y) :
    ∀ p q, A p q * x q = A p q * y q := by
  classical
  obtain ⟨N, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  intro p q
  let P (r : ℕ) : Prop := ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
    Fintype.card ι = r → ∀ (f : Option ι → Fin (N + 2)) (g : ι → Fin (N + 2)) (s : ℤˣ),
      weighted A f g q s x = weighted A f g q s y
  have missing (ι : Type) [Fintype ι] [DecidableEq ι]
      (hc : Fintype.card ι ≤ N) (f : Option ι → Fin (N + 2)) :
      ∃ τ, ∀ i, f i ≠ τ := by
    have hn : ¬ Function.Surjective f := by
      intro hf
      have hle := Fintype.card_le_of_surjective f hf
      simp only [Fintype.card_fin, Fintype.card_option] at hle
      omega
    simpa [Function.Surjective] using hn
  have hbase : P N := by
    intro ι _ _ hc f g s
    obtain ⟨τ, hτ⟩ := missing ι hc.le f
    exact top A hA f g q τ s x y hxy (by simp [hc]) hτ
  have hstep (r : ℕ) (hr : r < N) (ih : P (r + 1)) : P r := by
    intro ι _ _ hc f g s
    obtain ⟨τ, hτ⟩ := missing ι (by omega) f
    apply descend A hA f g q τ s x y hτ
    intro z
    exact ih (Option ι) (by simp [hc]) (Option.rec τ f) (Option.rec z g) (-s)
  have hzero : P 0 :=
    Nat.decreasingInduction' (fun r hr _ ih => hstep r hr ih) (Nat.zero_le N) hbase
  have he := hzero PEmpty.{1} rfl (fun _ => p) PEmpty.elim (-1)
  have heval (v : Fin (N + 2) → R) :
      weighted A (fun _ : Option PEmpty.{1} => p) PEmpty.elim q (-1) v = A p q * v q := by
    have hd (j : Fin (N + 2)) :
        (minor A (fun _ : Option PEmpty.{1} => p) PEmpty.elim j).detp
          (if j = q then 1 else -1) = if j = q then A p j else 0 := by
      by_cases hj : j = q <;> simp [hj, minor, detp_option_expand_col_none]
    simp only [weighted, neg_neg]
    simp_rw [hd]
    simp [ite_mul]
  simpa only [heval] using he

end TransposeSummandSeparation

theorem solution
    {R : Type*} [CommSemiring R] {n : Nat} (hn : 2 <= n)
    (A : Matrix (Fin n) (Fin n) R)
    (hA : Function.Injective A.transpose.mulVec)
    (x y : Fin n -> R) (hxy : A.mulVec x = A.mulVec y) :
    forall p q, A p q * x q = A p q * y q :=
  TransposeSummandSeparation.summand_separation hn A hA x y hxy
