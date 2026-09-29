-- Prove2me | solution 1 for flt5_ck5_conj_pair_prod
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-14T07:24:56.434759+00:00
-- url     : https://prove2.me/submissions/829c17c3-ff60-4ce0-8d3d-b171a2d222e9

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.FieldTheory.PrimitiveElement

noncomputable section

open NumberField ComplexEmbedding

abbrev CK5cpd := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5cpd :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5cpd :=
  IsCyclotomicExtension.numberField {5} ℚ CK5cpd

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

instance : IsTotallyComplex CK5cpd :=
  IsCyclotomicExtension.Rat.isTotallyComplex CK5cpd (by norm_num : 2 < 5)

-- σ(x) * star(σ(x)) = normSq(σ(x)) in ℂ
lemma mul_star_normSq_cpd (z : ℂ) : z * star z = (Complex.normSq z : ℂ) :=
  Complex.mul_conj z

-- conjugate is FP-free (totally complex)
lemma conj_ne_self_cpd (φ : CK5cpd →+* ℂ) : conjugate φ ≠ φ :=
  fun h => IsTotallyComplex.complexEmbedding_not_isReal φ (isReal_iff.mpr h)

-- conjugate is an involution
lemma conj_invol_cpd (φ : CK5cpd →+* ℂ) : conjugate (conjugate φ) = φ :=
  (involutive_conjugate CK5cpd) φ

-- Product over algebra homs = product over ring homs
lemma prod_algHom_eq_ringHom_cpd (x : CK5cpd) :
    ∏ σ : CK5cpd →ₐ[ℚ] ℂ, σ x = ∏ φ : CK5cpd →+* ℂ, φ x :=
  Fintype.prod_equiv RingHom.equivRatAlgHom.symm (fun σ => σ x) (fun φ => φ x)
    (fun _ => rfl)

-- Card of ring homs = 4
lemma card_ringHom_cpd : Fintype.card (CK5cpd →+* ℂ) = 4 := by
  rw [NumberField.Embeddings.card, IsCyclotomicExtension.finrank CK5cpd
    (Polynomial.cyclotomic.irreducible_rat (by norm_num : 0 < 5))]
  decide

theorem solution :
    ∃ (σ₁ σ₂ : CK5cpd →ₐ[ℚ] ℂ),
    ∀ (x : CK5cpd),
    (∏ σ : CK5cpd →ₐ[ℚ] ℂ, σ x) = ↑(Complex.normSq (σ₁ x) * Complex.normSq (σ₂ x)) := by
  haveI : DecidableEq (CK5cpd →+* ℂ) := Classical.decEq _
  have hcard : Fintype.card (CK5cpd →+* ℂ) = 4 := card_ringHom_cpd
  haveI hne : Nonempty (CK5cpd →+* ℂ) := by rw [← Fintype.card_pos_iff]; omega
  obtain ⟨φ₁⟩ := hne
  have h1ne : conjugate φ₁ ≠ φ₁ := conj_ne_self_cpd φ₁
  have h2card : ({φ₁, conjugate φ₁} : Finset _).card = 2 :=
    Finset.card_pair (Ne.symm h1ne)
  have hS : (Finset.univ (α := CK5cpd →+* ℂ) \ {φ₁, conjugate φ₁}).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, h2card, hcard]
    norm_num
  obtain ⟨φ₂, hφ₂⟩ := hS
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
             true_and, not_or] at hφ₂
  obtain ⟨hφ₂_ne1, hφ₂_ne1bar⟩ := hφ₂
  have h2ne : conjugate φ₂ ≠ φ₂ := conj_ne_self_cpd φ₂
  have hφ₂bar_ne1 : conjugate φ₂ ≠ φ₁ := by
    intro h; exact hφ₂_ne1bar (by rw [← conj_invol_cpd φ₂, h])
  have hφ₂bar_ne1bar : conjugate φ₂ ≠ conjugate φ₁ := by
    intro h; exact hφ₂_ne1 (by rw [← conj_invol_cpd φ₂, h, conj_invol_cpd])
  have hmem_a : φ₁ ∉ ({conjugate φ₁, φ₂, conjugate φ₂} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm h1ne, fun h => hφ₂_ne1 h.symm, fun h => hφ₂bar_ne1 h.symm⟩
  have hmem_b : conjugate φ₁ ∉ ({φ₂, conjugate φ₂} : Finset _) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => hφ₂_ne1bar h.symm, fun h => hφ₂bar_ne1bar h.symm⟩
  have hmem_c : φ₂ ∉ ({conjugate φ₂} : Finset _) := by
    simp only [Finset.mem_singleton]; exact Ne.symm h2ne
  have h4eq : ({φ₁, conjugate φ₁, φ₂, conjugate φ₂} : Finset _) =
      Finset.univ (α := CK5cpd →+* ℂ) := by
    apply Finset.eq_univ_of_card
    rw [show ({φ₁, conjugate φ₁, φ₂, conjugate φ₂} : Finset _) =
        insert φ₁ (insert (conjugate φ₁) (insert φ₂ {conjugate φ₂})) from rfl,
      Finset.card_insert_of_notMem hmem_a, Finset.card_insert_of_notMem hmem_b,
      Finset.card_insert_of_notMem hmem_c, Finset.card_singleton]
    omega
  let σ₁ : CK5cpd →ₐ[ℚ] ℂ := RingHom.equivRatAlgHom φ₁
  let σ₂ : CK5cpd →ₐ[ℚ] ℂ := RingHom.equivRatAlgHom φ₂
  refine ⟨σ₁, σ₂, fun x => ?_⟩
  rw [prod_algHom_eq_ringHom_cpd x, ← h4eq]
  rw [show ({φ₁, conjugate φ₁, φ₂, conjugate φ₂} : Finset _) =
      insert φ₁ (insert (conjugate φ₁) (insert φ₂ {conjugate φ₂})) from rfl,
    Finset.prod_insert hmem_a, Finset.prod_insert hmem_b,
    Finset.prod_insert hmem_c, Finset.prod_singleton]
  have heq1 : σ₁ x = φ₁ x := rfl
  have heq2 : σ₂ x = φ₂ x := rfl
  have hconj1 : (conjugate φ₁) x = star (φ₁ x) := conjugate_coe_eq φ₁ x
  have hconj2 : (conjugate φ₂) x = star (φ₂ x) := conjugate_coe_eq φ₂ x
  rw [hconj1, hconj2, ← heq1, ← heq2]
  rw [show σ₁ x * (star (σ₁ x) * (σ₂ x * star (σ₂ x))) =
      (σ₁ x * star (σ₁ x)) * (σ₂ x * star (σ₂ x)) by ring]
  rw [mul_star_normSq_cpd (σ₁ x), mul_star_normSq_cpd (σ₂ x)]
  push_cast
  ring

end
