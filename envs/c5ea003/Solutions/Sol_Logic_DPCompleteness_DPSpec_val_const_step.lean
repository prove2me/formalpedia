-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.val_const_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T01:58:44.609699+00:00
-- url     : https://prove2.me/submissions/a003b4ed-ad7d-49cc-b207-4a88851208fe

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessApplications
import Definitions.Def_Logic_DPCompletenessWalks
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    [AddLeftMono W] (D : DPSpec S W) (c : W) (h : ∀ i s t, D.step i s t = c) :
    ∀ (n : ℕ) (t : S),
      D.val (n + 1) t =
        (Finset.univ : Finset S).sup' Finset.univ_nonempty D.init + (n + 1) • c := by
  -- adding a constant on the right commutes with `sup'`
  have hsupadd : ∀ (f : S → W) (a : W),
      (Finset.univ : Finset S).sup' Finset.univ_nonempty (fun s => f s + a)
        = (Finset.univ : Finset S).sup' Finset.univ_nonempty f + a := by
    intro f a
    refine (Finset.comp_sup'_eq_sup'_comp Finset.univ_nonempty (fun w => w + a) ?_).symm
    intro x y
    rcases le_total x y with hxy | hxy
    · have hc : x + a ≤ y + a := by gcongr
      simp only [sup_eq_right.mpr hxy, sup_eq_right.mpr hc]
    · have hc : y + a ≤ x + a := by gcongr
      simp only [sup_eq_left.mpr hxy, sup_eq_left.mpr hc]
  intro n
  induction n with
  | zero =>
    intro t
    show (Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun s => D.val 0 s + D.step 0 s t) = _
    simp only [h, DPSpec.val, hsupadd]
    simp
  | succ n ih =>
    intro t
    show (Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun s => D.val (n + 1) s + D.step (n + 1) s t) = _
    simp only [h, ih, hsupadd, Finset.sup'_const, succ_nsmul]
    rw [add_assoc]
