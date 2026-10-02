-- Prove2me | solution 1 for BookSixth.latin_rectangle_extend
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T05:47:06.87862+00:00
-- url     : https://prove2.me/submissions/b953c479-fd19-4d61-9036-ca4a131c8fc6

import Mathlib
import Definitions.Def_BookSixth

open scoped BigOperators
open BookSixth

theorem solution (n k : ℕ) (hkn : k < n) :
    (Finset.univ.filter (fun R : Fin (k + 1) → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j)))).card
    = ∑ R ∈ Finset.univ.filter (fun R : Fin k → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j))),
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        ∀ j, ∀ i : Fin k, R i j ≠ σ j)).card := by
  classical
  set Sfilter : Finset (Fin (k + 1) → Fin n → Fin n) := Finset.univ.filter
    (fun R : Fin (k + 1) → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j))) with hSdef
  set Tfilter : Finset (Fin k → Fin n → Fin n) := Finset.univ.filter
    (fun R : Fin k → Fin n → Fin n =>
      (∀ i, Function.Bijective (R i)) ∧ (∀ j, Function.Injective (fun i => R i j))) with hTdef
  have hresT : Set.MapsTo
      (fun R : Fin (k + 1) → Fin n → Fin n => fun i j => R (Fin.castSucc i) j)
      Sfilter Tfilter := by
    intro R hR
    simp only [hSdef, hTdef, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_univ, true_and] at hR ⊢
    obtain ⟨hrow, hcol⟩ := hR
    exact ⟨fun i => hrow (Fin.castSucc i),
      fun j => (hcol j).comp (Fin.castSucc_injective k)⟩
  have hlast : ∀ R : Fin (k + 1) → Fin n → Fin n, R ∈ Sfilter →
      Function.Bijective (R (Fin.last k)) := by
    intro R hR
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hR
    exact hR.1 (Fin.last k)
  have hcolof : ∀ R : Fin (k + 1) → Fin n → Fin n, R ∈ Sfilter →
      ∀ j, Function.Injective (fun i => R i j) := by
    intro R hR
    simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at hR
    exact hR.2
  set fwd : (R : Fin (k + 1) → Fin n → Fin n) → R ∈ Sfilter →
      Σ _ : (Fin k → Fin n → Fin n), Equiv.Perm (Fin n) :=
    fun R hR => ⟨(fun i j => R (Fin.castSucc i) j),
      Equiv.ofBijective (R (Fin.last k)) (hlast R hR)⟩ with hfwd
  have hi : ∀ R : Fin (k + 1) → Fin n → Fin n, ∀ hR : R ∈ Sfilter,
      fwd R hR ∈ Finset.sigma Tfilter
      (fun (R₀ : Fin k → Fin n → Fin n) => Finset.univ.filter
        (fun σ : Equiv.Perm (Fin n) => ∀ j, ∀ i : Fin k, R₀ i j ≠ σ j)) := by
    intro R hR
    rw [Finset.mem_sigma]
    simp only [hfwd]
    show ((fun i j => R (Fin.castSucc i) j) ∈ Tfilter ∧
      Equiv.ofBijective (R (Fin.last k)) (hlast R hR) ∈ Finset.univ.filter _)
    refine ⟨Finset.mem_coe.mp (hresT (Finset.mem_coe.mpr hR)), ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro j i hij
    have e1 : R (Fin.castSucc i) j = R (Fin.last k) j := hij
    exact Fin.castSucc_ne_last i (hcolof R hR j e1)
  have hinj : ∀ R₁ : Fin (k + 1) → Fin n → Fin n, ∀ hR₁ : R₁ ∈ Sfilter,
      ∀ R₂ : Fin (k + 1) → Fin n → Fin n, ∀ hR₂ : R₂ ∈ Sfilter,
      fwd R₁ hR₁ = fwd R₂ hR₂ → R₁ = R₂ := by
    intro R hR₁ S hS₁ hEq
    have hFst := congrArg Sigma.fst hEq
    simp only [hfwd] at hFst
    have hSnd := congrArg Sigma.snd hEq
    simp only [hfwd] at hSnd
    have hlast_eq : ∀ j, R (Fin.last k) j = S (Fin.last k) j :=
      fun j => congrArg (fun e : Equiv.Perm (Fin n) => e j) hSnd
    funext i j
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · have h1 : R (Fin.castSucc i') j = (fun i j => R (Fin.castSucc i) j) i' j := rfl
      have h2 : S (Fin.castSucc i') j = (fun i j => S (Fin.castSucc i) j) i' j := rfl
      rw [h1, h2, hFst]
    · exact hlast_eq j
  have hsurj : ∀ p ∈ Finset.sigma Tfilter
      (fun (R₀ : Fin k → Fin n → Fin n) => Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => ∀ j, ∀ i : Fin k, R₀ i j ≠ σ j)),
      ∃ R : Fin (k + 1) → Fin n → Fin n, ∃ hR : R ∈ Sfilter, fwd R hR = p := by
    intro p hp
    rw [Finset.mem_sigma] at hp
    obtain ⟨hR₀mem, hσmem⟩ := hp
    obtain ⟨R₀, σ⟩ := p
    simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and] at hR₀mem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσmem
    obtain ⟨hR₀row, hR₀col⟩ := hR₀mem
    set R' : Fin (k + 1) → Fin n → Fin n := Fin.lastCases ⇑σ (fun i => R₀ i) with hR'
    have hR'row : ∀ i, Function.Bijective (R' i) := by
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
      · simp only [hR', Fin.lastCases_castSucc]; exact hR₀row i'
      · simp only [hR', Fin.lastCases_last]; exact σ.bijective
    have hR'col : ∀ j, Function.Injective (fun i => R' i j) := by
      intro j a b hab
      simp only [hR'] at hab
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · simp only [Fin.lastCases_castSucc] at hab
        rw [hR₀col j hab]
      · simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hab
        exact absurd hab (hσmem j a')
      · simp only [Fin.lastCases_last, Fin.lastCases_castSucc] at hab
        exact absurd hab.symm (hσmem j b')
      · rfl
    have hR'mem : R' ∈ Sfilter := by
      simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hR'row, hR'col⟩
    have hlastR' : R' (Fin.last k) = ⇑σ := by
      rw [hR']
      exact Fin.lastCases_last
    have hR'res : (fun i j => R' (Fin.castSucc i) j) = R₀ := by
      funext i j
      simp only [hR', Fin.lastCases_castSucc]
    have hperm : (Equiv.ofBijective (R' (Fin.last k)) (hlast R' hR'mem) : Equiv.Perm (Fin n))
        = σ := by
      apply Equiv.ext
      intro j
      show R' (Fin.last k) j = σ j
      rw [hlastR']
    refine ⟨R', hR'mem, ?_⟩
    have hfwd' : fwd R' hR'mem =
        (⟨(fun i j => R' (Fin.castSucc i) j),
          Equiv.ofBijective (R' (Fin.last k)) (hlast R' hR'mem)⟩ :
        Σ _ : (Fin k → Fin n → Fin n), Equiv.Perm (Fin n)) := rfl
    rw [hfwd', hR'res, hperm]
  rw [← Finset.card_sigma]
  exact Finset.card_bij fwd hi hinj hsurj
