-- Prove2me | solution 2 for PythHydra.exists_parent_ancestor
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T19:16:22.596183+00:00
-- url     : https://prove2.me/submissions/4337ce61-a51c-4aaf-9ab5-1f200179da07

import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraCalibration
import Definitions.Def_Geometry_PythagoreanHydra_HydraDepth
import Definitions.Def_Geometry_PythagoreanHydra_PythagoreanHydra
open PythHydra in
theorem solution {t : ℤ × ℤ × ℤ} (h : 0 < bergDepth t) :
    ∃ p, IsBergAncestor p t ∧ bergDepth p + 1 = bergDepth t := by
  have hppt : ∀ w : List BStep, IsPPT (addr w).1 (addr w).2.1 (addr w).2.2 := by
    intro w
    induction w with
    | nil => exact root_isPPT
    | cons s w ih =>
      cases s
      · exact bergA_isPPT ih
      · exact bergB_isPPT ih
      · exact bergC_isPPT ih
  have hgrowc : ∀ (s : BStep) (t : ℤ × ℤ × ℤ), IsPPT t.1 t.2.1 t.2.2 →
      t.2.2 < (applyStep s t).2.2 := by
    rintro s ⟨a, b, c⟩ h
    obtain ⟨hac, hbc⟩ := h.legs_lt
    have := h.ha
    have := h.hb
    cases s <;> simp only [applyStep, bergA_snd_snd, bergB_snd_snd, bergC_snd_snd] <;> linarith
  have hc5 : ∀ w : List BStep, 5 ≤ (addr w).2.2 := by
    intro w
    induction w with
    | nil => simp [addr]
    | cons s w ih =>
      have := hgrowc s (addr w) (hppt w)
      simp only [addr]
      linarith
  have hgt5 : ∀ (s : BStep) (w : List BStep), 5 < (addr (s :: w)).2.2 := by
    intro s w
    have := hgrowc s (addr w) (hppt w)
    have := hc5 w
    simp only [addr]
    linarith
  have habs1 : ∀ x y : ℤ, x = y → 0 < y → |x| = y := by
    intro x y h hy
    rw [h, abs_of_pos hy]
  have habs2 : ∀ x y : ℤ, x = -y → 0 < y → |x| = y := by
    intro x y h hy
    rw [h, abs_neg, abs_of_pos hy]
  have hpar : ∀ (s : BStep) (t : ℤ × ℤ × ℤ), 0 < t.1 → 0 < t.2.1 →
      parent (applyStep s t).1 (applyStep s t).2.1 (applyStep s t).2.2 = t := by
    rintro s ⟨a, b, c⟩ ha hb
    simp only at ha hb
    cases s <;> simp only [applyStep, parent, uu, vv, hh, bergA, bergB, bergC, Prod.mk.injEq] <;>
      refine ⟨?_, ?_, by ring⟩ <;>
      first
        | (refine habs1 _ _ ?_ (by assumption); ring1)
        | (refine habs2 _ _ ?_ (by assumption); ring1)
  have hstep_inj : ∀ (s₁ s₂ : BStep) (t : ℤ × ℤ × ℤ), 0 < t.1 → 0 < t.2.1 →
      applyStep s₁ t = applyStep s₂ t → s₁ = s₂ := by
    rintro s₁ s₂ ⟨a, b, c⟩ ha hb h
    simp only at ha hb
    cases s₁ <;> cases s₂ <;> simp only [applyStep, bergA, bergB, bergC, Prod.mk.injEq] at h <;>
      first | rfl | (exfalso; omega)
  have hinj : ∀ w₁ w₂ : List BStep, addr w₁ = addr w₂ → w₁ = w₂ := by
    intro w₁
    induction w₁ with
    | nil =>
      intro w₂ h
      cases w₂ with
      | nil => rfl
      | cons s w =>
        exfalso
        have := hgt5 s w
        rw [← h] at this
        simp [addr] at this
    | cons s₁ v₁ ih =>
      intro w₂ h
      cases w₂ with
      | nil =>
        exfalso
        have := hgt5 s₁ v₁
        rw [h] at this
        simp [addr] at this
      | cons s₂ v₂ =>
        simp only [addr] at h
        have hv : addr v₁ = addr v₂ := by
          calc addr v₁ = parent (applyStep s₁ (addr v₁)).1 (applyStep s₁ (addr v₁)).2.1
                (applyStep s₁ (addr v₁)).2.2 := (hpar s₁ (addr v₁) (hppt v₁).ha (hppt v₁).hb).symm
            _ = parent (applyStep s₂ (addr v₂)).1 (applyStep s₂ (addr v₂)).2.1
                (applyStep s₂ (addr v₂)).2.2 := by rw [h]
            _ = addr v₂ := hpar s₂ (addr v₂) (hppt v₂).ha (hppt v₂).hb
        have hvv := ih v₂ hv
        subst hvv
        rw [hstep_inj s₁ s₂ (addr v₁) (hppt v₁).ha (hppt v₁).hb h]
  have hreach_addr : ∀ t, Reach t → ∃ w : List BStep, addr w = t := by
    intro t ht
    induction ht with
    | root => exact ⟨[], rfl⟩
    | stepA _ ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨BStep.A :: w, by simp only [addr, applyStep, hw]⟩
    | stepB _ ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨BStep.B :: w, by simp only [addr, applyStep, hw]⟩
    | stepC _ ih =>
      obtain ⟨w, hw⟩ := ih
      exact ⟨BStep.C :: w, by simp only [addr, applyStep, hw]⟩
  have hexists : ∀ {a b c : ℤ}, IsPPT a b c → ∃ w : List BStep, addr w = (a, b, c) :=
    fun h => hreach_addr _ ((reach_iff_isPPT _ _ _).mpr h)
  have hdepth : ∀ w : List BStep, bergDepth (addr w) = w.length := by
    intro w
    have hex : ∃ w' : List BStep, addr w' = addr w := ⟨w, rfl⟩
    unfold bergDepth
    rw [dif_pos hex, hinj _ _ hex.choose_spec]
  have hdepth_parent : ∀ {a b c : ℤ}, IsPPT a b c → 5 < c →
      bergDepth (parent a b c) + 1 = bergDepth (a, b, c) := by
    intro a b c h hc
    obtain ⟨w, hw⟩ := hexists h
    cases w with
    | nil =>
      simp only [addr, Prod.mk.injEq] at hw
      omega
    | cons s v =>
      have hp := hpar s (addr v) (hppt v).ha (hppt v).hb
      have hw' : applyStep s (addr v) = (a, b, c) := hw
      rw [hw'] at hp
      simp only at hp
      rw [hp, ← hw, hdepth, hdepth]
      simp
  have hexpar : ∀ {t : ℤ × ℤ × ℤ}, 0 < bergDepth t →
      ∃ p, IsBergAncestor p t ∧ bergDepth p + 1 = bergDepth t := by
    intro t h
    by_cases hex : ∃ w : List BStep, addr w = t
    · obtain ⟨w, rfl⟩ := hex
      rw [hdepth] at h
      cases w with
      | nil => simp at h
      | cons s v =>
        refine ⟨addr v, Relation.TransGen.single ⟨hppt (s :: v), hgt5 s v, ?_⟩, ?_⟩
        · exact (hpar s (addr v) (hppt v).ha (hppt v).hb).symm
        · rw [hdepth, hdepth]
          simp
    · exfalso
      unfold bergDepth at h
      rw [dif_neg hex] at h
      omega
  exact hexpar h
