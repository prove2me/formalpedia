-- Prove2me | solution 2 for Cryptography.BerggrenModular.recoverMod_applyWordM
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T18:07:05.274774+00:00
-- url     : https://prove2.me/submissions/5c9dbd9f-85b0-4345-9dca-8c641f6a6b7e

import Mathlib
import Definitions.Def_Cryptography_BerggrenModular_Core
import Definitions.Def_Cryptography_BerggrenModular_Modular
open Cryptography BerggrenModular in
theorem solution {m : ℕ} [NeZero m] (u : List Move) {v : Tri} (hv : Valid v)
    (hb : ∀ s : List Move, s <:+ u → (applyWord s v).2.2 < m) :
    recoverMod m u.length (redTri m (applyWord u v)) = u := by
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
  induction u with
  | nil => rfl
  | cons i w ih =>
    have hw : Valid (applyWord w v) := hwvalid w v hv
    have hbi : (applyMove i (applyWord w v)).2.2 < m := hb (i :: w) (List.suffix_refl _)
    have hwhm := hwhichMod i (applyWord w v) hw hbi
    simp only [List.length_cons, applyWord]
    rw [recoverMod, hwhm, ← hredinv, hinv,
      ih (fun s hs => hb s (hs.trans (List.suffix_cons i w)))]
