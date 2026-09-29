-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.bval_eq_sup_walk
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:49:21.981802+00:00
-- url     : https://prove2.me/submissions/4eb781ce-83f6-4870-be92-1774ae3fc945

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessWalks
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    [AddLeftMono W] (D : DPSpec S W) :
    ∀ (m k : ℕ) (s : S),
      D.bval k (m + 1) s =
        (Finset.univ : Finset S).sup' Finset.univ_nonempty (fun t => D.walk k m s t) := by
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
  intro m
  induction m with
  | zero =>
    intro k s
    show (Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun t => D.step k s t + D.bval (k + 1) 0 t) = _
    simp only [DPSpec.bval, DPSpec.walk, add_zero]
  | succ m ih =>
    intro k s
    show (Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun t => D.step k s t + D.bval (k + 1) (m + 1) t) = _
    have hL : ∀ t : S, D.step k s t + D.bval (k + 1) (m + 1) t
        = (Finset.univ : Finset S).sup' Finset.univ_nonempty
            (fun u => D.step k s t + D.walk (k + 1) m t u) := by
      intro t
      rw [ih (k + 1) t, hadd_sup]
    rw [Finset.sup'_congr Finset.univ_nonempty rfl (fun t _ => hL t)]
    rw [Finset.sup'_comm]
    rfl
