-- Prove2me | solution 2 for PythHydra.berg_step_depth_pred
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T19:20:48.212359+00:00
-- url     : https://prove2.me/submissions/95790777-6e36-45f8-91e8-610f4591b2b0

import Mathlib
import Definitions.Def_Geometry_PythagoreanHydra_HydraCalibration
import Definitions.Def_Geometry_PythagoreanHydra_HydraDepth
import Definitions.Def_Geometry_PythagoreanHydra_HydraGame
import Definitions.Def_Geometry_PythagoreanHydra_PythagoreanHydra
open PythHydra in
theorem solution {k : ℕ} {H : Multiset (ℤ × ℤ × ℤ)} (hH : H ≠ 0) :
    ∃ H', BergChop k H H' ∧ Phi k (H'.map bergDepth) + 1 = Phi k (H.map bergDepth) := by
  have hphi_zero : phi k 0 = 1 := by simp [phi]
  have hphi_succ : ∀ n : ℕ, phi k (n + 1) = 1 + k * phi k n := by
    intro n
    unfold phi
    rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hphi_mono : ∀ a b : ℕ, a ≤ b → phi k a ≤ phi k b := by
    intro a b hab
    unfold phi
    exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
  have hphi_pos : ∀ n : ℕ, 1 ≤ phi k n := by
    intro n
    cases n with
    | zero => rw [hphi_zero]
    | succ n => rw [hphi_succ]; omega
  have hPhi_cons : ∀ (m : ℕ) (H : Multiset ℕ), Phi k (m ::ₘ H) = phi k m + Phi k H := by
    intro m H
    simp [Phi]
  have hPhi_add : ∀ A B : Multiset ℕ, Phi k (A + B) = Phi k A + Phi k B := by
    intro A B
    simp [Phi]
  have hPhi_nil : Phi k 0 = 0 := by simp [Phi]
  have hPhi_rep : ∀ c n : ℕ, Phi k (Multiset.replicate c n) = c * phi k n := by
    intro c n
    simp [Phi, Multiset.map_replicate, Multiset.sum_replicate]
  have hPhi_eq_zero : ∀ H : Multiset ℕ, Phi k H = 0 → H = 0 := by
    intro H hH
    induction H using Multiset.induction_on with
    | empty => rfl
    | cons m H _ =>
      rw [hPhi_cons] at hH
      have := hphi_pos m
      omega
  have hPhi_le : ∀ (H : Multiset ℕ) (L : ℕ), (∀ x ∈ H, x ≤ L) → Phi k H ≤ Multiset.card H * phi k L := by
    intro H L hL
    unfold Phi
    have := Multiset.sum_le_card_nsmul (H.map (phi k)) (phi k L) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      exact hphi_mono x L (hL x hx))
    simpa using this
  have hPhi_R : ∀ (m : ℕ) (R : Multiset ℕ), (∀ x ∈ R, x < m) → Multiset.card R ≤ k →
      Phi k R + 1 ≤ phi k m := by
    intro m R hlt hcard
    cases m with
    | zero =>
      have hR : R = 0 := Multiset.eq_zero_of_forall_notMem (fun x hx => by
        have := hlt x hx
        omega)
      subst hR
      rw [hPhi_nil, hphi_zero]
    | succ n =>
      have h1 := hPhi_le R n (fun x hx => by have := hlt x hx; omega)
      have h2 : Multiset.card R * phi k n ≤ k * phi k n := Nat.mul_le_mul_right _ hcard
      rw [hphi_succ]
      omega
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
  have hanc : ∀ s t : ℤ × ℤ × ℤ, IsBergAncestor s t → bergDepth s < bergDepth t := by
    intro s t h
    induction h with
    | single hst =>
      obtain ⟨hp, hc, rfl⟩ := hst
      have := hdepth_parent hp hc
      simp only [Prod.mk.eta] at this
      omega
    | tail _ hbc ih =>
      obtain ⟨hp, hc, rfl⟩ := hbc
      have := hdepth_parent hp hc
      simp only [Prod.mk.eta] at this
      omega
  have hchop_ex : ∀ H : Multiset (ℤ × ℤ × ℤ), H ≠ 0 →
      ∃ H', BergChop k H H' ∧ Phi k (H'.map bergDepth) + 1 = Phi k (H.map bergDepth) := by
    intro H hH
    obtain ⟨t, ht⟩ := Multiset.exists_mem_of_ne_zero hH
    obtain ⟨H₀, rfl⟩ := Multiset.exists_cons_of_mem ht
    rcases Nat.eq_zero_or_pos (bergDepth t) with h0 | hpos
    · refine ⟨0 + H₀, BergChop.chop t H₀ 0 (by simp) (by simp), ?_⟩
      rw [Multiset.map_add, Multiset.map_cons, hPhi_add, hPhi_cons, h0, hphi_zero,
        Multiset.map_zero, hPhi_nil]
      omega
    · obtain ⟨p, hp, hdp⟩ := hexpar hpos
      refine ⟨Multiset.replicate k p + H₀, BergChop.chop t H₀ _
        (fun s hs => by rw [Multiset.eq_of_mem_replicate hs]; exact hp) (by simp), ?_⟩
      rw [Multiset.map_add, Multiset.map_cons, Multiset.map_replicate, hPhi_add, hPhi_cons,
        hPhi_rep, ← hdp, hphi_succ]
      ring
  exact hchop_ex H hH
