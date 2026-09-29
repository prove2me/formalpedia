-- Prove2me | solution 2 for Cryptography.BerggrenModular.applyWord_injective
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T18:01:56.546767+00:00
-- url     : https://prove2.me/submissions/d91d05a3-8f24-4eb1-a0d8-352a9291b958

import Definitions.Def_Cryptography_BerggrenModular_Core
open Cryptography.BerggrenModular in
theorem solution {v : Tri} (h : Valid v) :
    Function.Injective (fun w : List Move => applyWord w v) := by
  have hbasic : ∀ v : Tri, Valid v → v.1 < v.2.2 ∧ v.2.1 < v.2.2 ∧ v.2.2 < v.1 + v.2.1 := by
    rintro ⟨a, b, c⟩ ⟨ha, hb, hc, hp⟩
    simp only at *
    refine ⟨by nlinarith, by nlinarith, by nlinarith⟩
  have hvalid : ∀ (i : Move) (v : Tri), Valid v → Valid (applyMove i v) := by
    rintro i ⟨a, b, c⟩ hv
    obtain ⟨h1, h2, h3⟩ := hbasic _ hv
    obtain ⟨ha, hb, hc, hp⟩ := hv
    simp only at *
    cases i <;> simp only [applyMove, Valid] <;> refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  have hlt : ∀ (i : Move) (v : Tri), Valid v → v.2.2 < (applyMove i v).2.2 := by
    rintro i ⟨a, b, c⟩ hv
    obtain ⟨h1, h2, h3⟩ := hbasic _ hv
    obtain ⟨ha, hb, hc, hp⟩ := hv
    simp only at *
    cases i <;> simp only [applyMove] <;> nlinarith
  have hwvalid : ∀ (w : List Move) (v : Tri), Valid v → Valid (applyWord w v) := by
    intro w v hv
    induction w with
    | nil => exact hv
    | cons i w ih => exact hvalid i _ ih
  have hwle : ∀ (w : List Move) (v : Tri), Valid v → v.2.2 ≤ (applyWord w v).2.2 := by
    intro w v hv
    induction w with
    | nil => exact le_refl _
    | cons i w ih => exact ih.trans (hlt i _ (hwvalid w v hv)).le
  have hwhich : ∀ (i : Move) (v : Tri), Valid v → whichMove (applyMove i v) = i := by
    rintro i ⟨a, b, c⟩ hv
    obtain ⟨h1, h2, h3⟩ := hbasic _ hv
    obtain ⟨ha, hb, hc, hp⟩ := hv
    simp only at *
    cases i <;> simp only [whichMove, applyMove] <;> split_ifs <;> first | rfl | (exfalso; linarith)
  have hinv : ∀ (i : Move) (v : Tri), invMove i (applyMove i v) = v := by
    rintro i ⟨a, b, c⟩
    cases i <;> simp only [invMove, applyMove] <;> ext <;> simp <;> ring
  intro w₁
  induction w₁ with
  | nil =>
    intro w₂ heq
    cases w₂ with
    | nil => rfl
    | cons j w₂ =>
      exfalso
      simp only [applyWord] at heq
      have h1 := hlt j _ (hwvalid w₂ v h)
      have h2 := hwle w₂ v h
      rw [← heq] at h1
      linarith
  | cons i w₁ ih =>
    intro w₂ heq
    cases w₂ with
    | nil =>
      exfalso
      simp only [applyWord] at heq
      have h1 := hlt i _ (hwvalid w₁ v h)
      have h2 := hwle w₁ v h
      rw [heq] at h1
      linarith
    | cons j w₂ =>
      simp only [applyWord] at heq
      have hij : i = j := by
        have h1 := hwhich i _ (hwvalid w₁ v h)
        have h2 := hwhich j _ (hwvalid w₂ v h)
        rw [heq] at h1
        rw [← h1, h2]
      subst hij
      have hw : applyWord w₁ v = applyWord w₂ v := by
        have := congrArg (invMove i) heq
        rwa [hinv, hinv] at this
      rw [ih hw]
