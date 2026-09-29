-- Prove2me | solution 1 for Cryptography.BerggrenModular.recoverModFrom_correct
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T18:12:04.956061+00:00
-- url     : https://prove2.me/submissions/ea3e9795-9f79-4e68-87b6-deaf87e2621e

import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Hardness
import Definitions.Def_Cryptography_BerggrenModular_Threshold
open Cryptography BerggrenModular in
theorem solution {m k : ℕ} [NeZero m] (hm : 5 * 7 ^ k < m) :
    ∀ (n : ℕ) (u : List Move), u.length ≤ n → n ≤ k → recoverModFrom m n (stateMod m u) = u := by
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
  have hcast : ∀ x : ℤ, 0 ≤ x → x < m → (((x : ZMod m).val : ℕ) : ℤ) = x := by
    intro x h0 h1
    rw [ZMod.val_intCast]
    exact Int.emod_eq_of_lt h0 h1
  have hlift : ∀ x : Tri, 0 ≤ x.1 → x.1 < m → 0 ≤ x.2.1 → x.2.1 < m → 0 ≤ x.2.2 → x.2.2 < m →
      liftTri m (redTri m x) = x := by
    rintro ⟨a, b, c⟩ h1 h2 h3 h4 h5 h6
    simp only [liftTri, redTri] at *
    rw [hcast a h1 h2, hcast b h3 h4, hcast c h5 h6]
  have hliftV : ∀ x : Tri, Valid x → x.2.2 < m → liftTri m (redTri m x) = x := by
    intro x hx hm
    obtain ⟨h1, h2, h3⟩ := hbasic x hx
    obtain ⟨p1, p2, p3, _⟩ := hx
    exact hlift x p1.le (by linarith) p2.le (by linarith) p3.le hm
  have hwhichMod : ∀ (i : Move) (v : Tri), Valid v → (applyMove i v).2.2 < m →
      whichMoveMod m (redTri m (applyMove i v)) = i := by
    intro i v hv hb
    unfold whichMoveMod
    rw [hliftV _ (hvalid i v hv) hb]
    exact hwhich i v hv
  have hredinv : ∀ (i : Move) (y : Tri), redTri m (invMove i y) = invMoveM m i (redTri m y) := by
    rintro i ⟨a, b, c⟩
    cases i <;> simp only [redTri, invMove, invMoveM, Prod.mk.injEq] <;> push_cast <;> ring_nf <;> simp
  have hgrow : ∀ (i : Move) (v : Tri), Valid v → (applyMove i v).2.2 ≤ 7 * v.2.2 := by
    rintro i ⟨a, b, c⟩ hv
    obtain ⟨h1, h2, h3⟩ := hbasic _ hv
    obtain ⟨ha, hb, hc, hp⟩ := hv
    simp only at *
    cases i <;> simp only [applyMove] <;> nlinarith
  have hbound : ∀ u : List Move, (applyWord u root).2.2 ≤ 5 * 7 ^ u.length := by
    intro u
    induction u with
    | nil => simp [applyWord, root]
    | cons i w ih =>
      simp only [applyWord, List.length_cons, pow_succ]
      have := hgrow i _ (hwvalid w root hroot)
      nlinarith
  have hmZ : (5 * 7 ^ k : ℤ) < m := by exact_mod_cast hm
  have hlt_m : ∀ u : List Move, u.length ≤ k → (applyWord u root).2.2 < m := by
    intro u hu
    have h1 := hbound u
    have h2 : (7 : ℤ) ^ u.length ≤ 7 ^ k := pow_le_pow_right₀ (by norm_num) hu
    linarith
  intro n
  induction n with
  | zero =>
    intro u hu _
    have : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rfl
  | succ n ih =>
    intro u hu hnk
    cases u with
    | nil => simp [recoverModFrom, stateMod, applyWord]
    | cons i w =>
      have hw : w.length ≤ n := by simp at hu; omega
      have hwk : (i :: w).length ≤ k := by omega
      have hbi : (applyMove i (applyWord w root)).2.2 < m := hlt_m (i :: w) hwk
      have hvw := hwvalid w root hroot
      have hneq : stateMod m (i :: w) ≠ redTri m root := by
        intro heq
        have e1 := hliftV _ (hwvalid (i :: w) root hroot) (hlt_m _ hwk)
        have e2 := hliftV root hroot (by
          have := hwle (i :: w) root hroot
          linarith [hlt_m _ hwk])
        exact hne (i :: w) (List.cons_ne_nil i w) (by
          unfold stateMod at heq
          rw [← e1, heq, e2])
      rw [recoverModFrom, if_neg hneq]
      unfold stateMod
      simp only [applyWord]
      rw [hwhichMod i _ hvw hbi, ← hredinv, hinv]
      rw [show redTri m (applyWord w root) = stateMod m w from rfl, ih w hw (by omega)]
