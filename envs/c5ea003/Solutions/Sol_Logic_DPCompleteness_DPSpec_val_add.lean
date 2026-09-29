-- Prove2me | solution 1 for Logic.DPCompleteness.DPSpec.val_add
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T02:06:12.158677+00:00
-- url     : https://prove2.me/submissions/2f30c6f5-92b6-4c19-8ca8-463b4cefffd8

import Mathlib
import Definitions.Def_Logic_DPCompleteness
import Definitions.Def_Logic_DPCompletenessWalks
open Logic.DPCompleteness in
theorem solution {S W : Type*} [AddCommMonoid W] [Fintype S] [Nonempty S] [LinearOrder W]
    [AddLeftMono W] (D : DPSpec S W) :
    ∀ (m k : ℕ) (t : S),
      D.val (k + m + 1) t =
        (Finset.univ : Finset S).sup' Finset.univ_nonempty
          (fun s => D.val k s + D.walk k m s t) := by
  have hck : ∀ (m₁ m₂ k : ℕ) (s u : S),
      D.walk k (m₁ + m₂ + 1) s u =
        (Finset.univ : Finset S).sup' Finset.univ_nonempty
          (fun t => D.walk k m₁ s t + D.walk (k + m₁ + 1) m₂ t u) := by
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
    intro m₁
    induction m₁ with
    | zero =>
      intro m₂ k s u
      simp only [Nat.zero_add, Nat.add_zero, DPSpec.walk]
    | succ m₁ ih =>
      intro m₂ k s u
      have hidx : (m₁ + 1) + m₂ + 1 = (m₁ + m₂ + 1) + 1 := by omega
      have hidx2 : (k + 1) + m₁ + 1 = k + (m₁ + 1) + 1 := by omega
      rw [hidx]
      show (Finset.univ : Finset S).sup' Finset.univ_nonempty
          (fun v => D.step k s v + D.walk (k + 1) (m₁ + m₂ + 1) v u) = _
      have hL : ∀ v : S, D.step k s v + D.walk (k + 1) (m₁ + m₂ + 1) v u
          = (Finset.univ : Finset S).sup' Finset.univ_nonempty
              (fun t => D.step k s v + (D.walk (k + 1) m₁ v t
                + D.walk (k + (m₁ + 1) + 1) m₂ t u)) := by
        intro v
        rw [ih m₂ (k + 1) v u, hadd_sup, hidx2]
      rw [Finset.sup'_congr Finset.univ_nonempty rfl (fun v _ => hL v)]
      have hR : ∀ t : S, D.walk k (m₁ + 1) s t + D.walk (k + (m₁ + 1) + 1) m₂ t u
          = (Finset.univ : Finset S).sup' Finset.univ_nonempty
              (fun v => D.step k s v + D.walk (k + 1) m₁ v t
                + D.walk (k + (m₁ + 1) + 1) m₂ t u) := by
        intro t
        show ((Finset.univ : Finset S).sup' Finset.univ_nonempty
            (fun v => D.step k s v + D.walk (k + 1) m₁ v t))
            + D.walk (k + (m₁ + 1) + 1) m₂ t u = _
        rw [hsup_add]
      rw [Finset.sup'_congr Finset.univ_nonempty rfl (fun t _ => hR t)]
      rw [Finset.sup'_comm]
      refine Finset.sup'_congr Finset.univ_nonempty rfl (fun t _ => ?_)
      refine Finset.sup'_congr Finset.univ_nonempty rfl (fun v _ => ?_)
      exact (add_assoc _ _ _).symm
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
  -- the last-step decomposition of an optimal walk
  have hwalk_right : ∀ (m k : ℕ) (s t : S),
      D.walk k (m + 1) s t
        = (Finset.univ : Finset S).sup' Finset.univ_nonempty
            (fun u => D.walk k m s u + D.step (k + m + 1) u t) := by
    intro m k s t
    have h := hck m 0 k s t
    simpa [DPSpec.walk] using h
  intro m
  induction m with
  | zero =>
    intro k t
    simp only [Nat.add_zero, DPSpec.val, DPSpec.walk]
  | succ m ih =>
    intro k t
    have hidx : k + (m + 1) + 1 = (k + m + 1) + 1 := by omega
    rw [hidx]
    show (Finset.univ : Finset S).sup' Finset.univ_nonempty
        (fun u => D.val (k + m + 1) u + D.step (k + m + 1) u t) = _
    have hL : ∀ u : S, D.val (k + m + 1) u + D.step (k + m + 1) u t
        = (Finset.univ : Finset S).sup' Finset.univ_nonempty
            (fun s => D.val k s + D.walk k m s u + D.step (k + m + 1) u t) := by
      intro u
      rw [ih k u, hsup_add]
    rw [Finset.sup'_congr Finset.univ_nonempty rfl (fun u _ => hL u)]
    have hR : ∀ s : S, D.val k s + D.walk k (m + 1) s t
        = (Finset.univ : Finset S).sup' Finset.univ_nonempty
            (fun u => D.val k s + (D.walk k m s u + D.step (k + m + 1) u t)) := by
      intro s
      rw [hwalk_right m k s t, hadd_sup]
    rw [Finset.sup'_congr Finset.univ_nonempty rfl (fun s _ => hR s)]
    rw [Finset.sup'_comm]
    refine Finset.sup'_congr Finset.univ_nonempty rfl (fun s _ => ?_)
    refine Finset.sup'_congr Finset.univ_nonempty rfl (fun u _ => ?_)
    simp [add_assoc]
