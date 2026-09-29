-- Prove2me | solution 2 for Cryptography.BerggrenModular.recoverFrom_correct
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T18:17:38.015102+00:00
-- url     : https://prove2.me/submissions/a065b339-2f7f-425f-865d-cbe51aaeb3ad

import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Hardness
import Definitions.Def_Cryptography_BerggrenModular_Modular
open Cryptography BerggrenModular in
theorem solution : ∀ (n : ℕ) (u : List Move), u.length ≤ n →
    recoverFrom n (applyWord u root) = u := by
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
  have hroot : Valid root := by norm_num [Valid, root]
  have hne : ∀ u : List Move, u ≠ [] → applyWord u root ≠ root := by
    intro u hu heq
    cases u with
    | nil => exact hu rfl
    | cons i w =>
      have h1 := hlt i _ (hwvalid w root hroot)
      have h2 := hwle w root hroot
      simp only [applyWord] at heq
      rw [heq] at h1
      linarith
  intro n
  induction n with
  | zero =>
    intro u hu
    have : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro u hu
    cases u with
    | nil => simp [recoverFrom, applyWord]
    | cons i w =>
      have hne' := hne (i :: w) (List.cons_ne_nil i w)
      have hw : w.length ≤ n := by simp at hu; omega
      rw [recoverFrom, if_neg hne']
      simp only [applyWord]
      rw [hwhich i _ (hwvalid w root hroot), hinv, ih w hw]
