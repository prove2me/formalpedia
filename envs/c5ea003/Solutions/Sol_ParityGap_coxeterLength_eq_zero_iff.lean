-- Prove2me | solution 1 for ParityGap.coxeterLength_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:54:04.922546+00:00
-- url     : https://prove2.me/submissions/386024a1-facc-4f4a-9c85-cbb7dfa8da7f

-- Sol generated from Probability/CoxeterLength.lean
import Mathlib
import Definitions.Def_Probability_CoxeterLength
/-
# Coxeter length on the symmetric group and the sign character

The refinement asked for in Conjecture A speaks of a permutation of *minimal Coxeter length*.
This file supplies the notion and its basic theory in the shape needed there:

* `ParityGap.coxeterLength σ` — the number of inversions of `σ`, i.e. the length of `σ` in the
  Coxeter presentation of the symmetric group by adjacent transpositions;
* `ParityGap.sign_eq_neg_one_pow_coxeterLength` — the sign character is the parity of the
  Coxeter length;
* `ParityGap.coxeterLength_eq_zero_iff` — only the identity has length `0`.
-/


open Equiv Equiv.Perm Finset

open ParityGap

variable {n : ℕ}





@[simp] theorem coxeterLength_one : coxeterLength (1 : Perm (Fin n)) = 0 := by
  classical
  rw [coxeterLength, inversions, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x hx
  have hlt : x.2 < x.1 := Equiv.Perm.mem_finPairsLT.mp hx
  simpa using hlt.le



open ParityGap in
theorem solution{σ : Perm (Fin n)} : coxeterLength σ = 0 ↔ σ = 1 := by
  classical
  constructor
  · intro h
    have hno : ∀ x ∈ Equiv.Perm.finPairsLT n, ¬ (σ x.1 < σ x.2) := by
      intro x hx hlt
      have : x ∈ inversions σ := Finset.mem_filter.mpr ⟨hx, hlt⟩
      rw [coxeterLength, Finset.card_eq_zero] at h
      simp [h] at this
    have hmono : StrictMono σ := by
      intro a b hab
      have hmem : (⟨b, a⟩ : Σ _ : Fin n, Fin n) ∈ Equiv.Perm.finPairsLT n :=
        Equiv.Perm.mem_finPairsLT.mpr hab
      have := hno _ hmem
      have hne : σ b ≠ σ a := fun hc => absurd (σ.injective hc) (ne_of_gt hab)
      exact lt_of_le_of_ne (not_lt.mp this) (Ne.symm hne)
    -- a strictly monotone permutation of a finite linear order is the identity
    ext a
    have hiso : ∀ a : Fin n, a ≤ σ a := fun a => hmono.le_apply
    have hiso' : ∀ a : Fin n, a ≤ σ.symm a := by
      intro a
      have hmono' : StrictMono σ.symm := by
        intro x y hxy
        by_contra hc
        push_neg at hc
        rcases eq_or_lt_of_le hc with h1 | h1
        · exact absurd (σ.symm.injective h1) (ne_of_lt hxy).symm
        · have := hmono h1
          simp only [Equiv.apply_symm_apply] at this
          exact absurd this (not_lt.mpr hxy.le)
      exact hmono'.le_apply
    have h1 : a ≤ σ a := hiso a
    have h3 : σ a ≤ a := by
      have := hiso' (σ a)
      simpa using this
    exact le_antisymm h3 h1
  · rintro rfl
    exact coxeterLength_one
