-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.forward_backward
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T07:36:55.106328+00:00
-- url     : https://prove2.me/submissions/acbe2879-f837-47ed-bd1f-b59bf14bb483

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessWalks
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    [AddLeftMono W] [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    [Fintype S] [Nonempty S] [LinearOrder W] [IsOrderedCancelAddMonoid W]
    [Fintype S] [Nonempty S] [LinearOrder W] [AddLeftMono W]
    (D : DPSpec S W) :
    ∀ (m k : ℕ),
      (Finset.univ : Finset S).sup' Finset.univ_nonempty (fun s => D.val (k + m) s) =
        (Finset.univ : Finset S).sup' Finset.univ_nonempty
          (fun s => D.val k s + D.bval k m s) := by
  have hmono : ∀ (g : W → W), (∀ x y : W, g (x ⊔ y) = g x ⊔ g y) → ∀ f : S → W,
      g ((Finset.univ : Finset S).sup' Finset.univ_nonempty f)
        = (Finset.univ : Finset S).sup' Finset.univ_nonempty (fun i => g (f i)) := by
    intro g hg f
    exact Finset.comp_sup'_eq_sup'_comp Finset.univ_nonempty g hg
  have hadd_sup : ∀ (c : W) (f : S → W),
      c + (Finset.univ : Finset S).sup' Finset.univ_nonempty f
        = (Finset.univ : Finset S).sup' Finset.univ_nonempty (fun i => c + f i) := by
    intro c f
    refine hmono (fun w => c + w) ?_ f
    intro x y
    rcases le_total x y with hxy | hxy
    · have hc : c + x ≤ c + y := by gcongr
      simp only [sup_eq_right.mpr hxy, sup_eq_right.mpr hc]
    · have hc : c + y ≤ c + x := by gcongr
      simp only [sup_eq_left.mpr hxy, sup_eq_left.mpr hc]
  have hsup_add : ∀ (f : S → W) (c : W),
      (Finset.univ : Finset S).sup' Finset.univ_nonempty f + c
        = (Finset.univ : Finset S).sup' Finset.univ_nonempty (fun i => f i + c) := by
    intro f c
    refine hmono (fun w => w + c) ?_ f
    intro x y
    rcases le_total x y with hxy | hxy
    · have hc : x + c ≤ y + c := by gcongr
      simp only [sup_eq_right.mpr hxy, sup_eq_right.mpr hc]
    · have hc : y + c ≤ x + c := by gcongr
      simp only [sup_eq_left.mpr hxy, sup_eq_left.mpr hc]
  intro m
  induction m with
  | zero =>
    intro k
    simp only [Nat.add_zero, DPSpec.bval, add_zero]
  | succ m ih =>
    intro k
    have hidx : k + (m + 1) = (k + 1) + m := by omega
    rw [hidx, ih (k + 1)]
    have hR : ∀ s : S, D.val k s + D.bval k (m + 1) s
        = (Finset.univ : Finset S).sup' Finset.univ_nonempty
            (fun t => D.val k s + (D.step k s t + D.bval (k + 1) m t)) := by
      intro s
      show D.val k s + (Finset.univ : Finset S).sup' Finset.univ_nonempty
          (fun t => D.step k s t + D.bval (k + 1) m t) = _
      rw [hadd_sup]
    rw [Finset.sup'_congr Finset.univ_nonempty rfl (fun s _ => hR s), Finset.sup'_comm]
    refine Finset.sup'_congr Finset.univ_nonempty rfl (fun t _ => ?_)
    show (Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun s => D.val k s + D.step k s t) + D.bval (k + 1) m t = _
    rw [hsup_add]
    refine Finset.sup'_congr Finset.univ_nonempty rfl (fun s _ => ?_)
    exact add_assoc _ _ _
