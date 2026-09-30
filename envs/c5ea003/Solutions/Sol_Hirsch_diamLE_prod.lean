-- Prove2me | solution 1 for Hirsch.diamLE_prod
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T06:37:48.72841+00:00
-- url     : https://prove2.me/submissions/3c3c3a9a-8bc0-43f0-a561-0342316e7da9

import Definitions.Def_Hirsch_model
import Mathlib.Analysis.Convex.Extreme

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Set Hirsch

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

theorem adj_prod_left {P : Set E} {Q : Set F} {x y : E} {q : F}
    (hq : q ∈ extremePoints ℝ Q) (h : Adj P x y) :
    Adj (P ×ˢ Q) (x, q) (y, q) := by
  have hne : (x, q) ≠ (y, q) := by
    intro hxy
    exact h.1 (Prod.mk.inj hxy).1
  have hqQ : q ∈ Q := extremePoints_subset hq
  have hsubset : segment ℝ (x, q) (y, q) ⊆ P ×ˢ Q := by
    intro z hz
    have hz' : z ∈ (fun a => (a, q)) '' segment ℝ x y := by
      simpa [Prod.image_mk_segment_left] using hz
    obtain ⟨a, ha, rfl⟩ := hz'
    exact ⟨h.2.1 ha, hqQ⟩
  refine ⟨hne, hsubset, ?_⟩
  intro p1 hp1 p2 hp2 z hz hzopen
  have hz2 : z.2 = q := by
    have hz' : z ∈ (fun a => (a, q)) '' segment ℝ x y := by
      simpa [Prod.image_mk_segment_left] using hz
    obtain ⟨a, ha, rfl⟩ := hz'
    rfl
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hzopen
  have h2 : α • p1.2 + β • p2.2 = q := by
    have := congrArg Prod.snd hcomb
    simpa [hz2] using this
  have hop2 : q ∈ openSegment ℝ p1.2 p2.2 := ⟨α, β, hα, hβ, hαβ, h2⟩
  have hp1q : p1.2 = q := hq.2 hp1.2 hp2.2 hop2
  have hp2q : p2.2 = q := by
    have hop2' : q ∈ openSegment ℝ p2.2 p1.2 := by
      simpa [openSegment_symm] using hop2
    exact hq.2 hp2.2 hp1.2 hop2'
  have hz1 : z.1 ∈ segment ℝ x y := by
    have hz' : z ∈ (fun a => (a, q)) '' segment ℝ x y := by
      simpa [Prod.image_mk_segment_left] using hz
    obtain ⟨a, ha, hza⟩ := hz'
    have : z.1 = a := by
      have := congrArg Prod.fst hza
      exact this.symm
    simpa [this] using ha
  have hop1 : z.1 ∈ openSegment ℝ p1.1 p2.1 := by
    refine ⟨α, β, hα, hβ, hαβ, ?_⟩
    have := congrArg Prod.fst hcomb
    simpa using this
  have hp11 : p1.1 ∈ segment ℝ x y :=
    h.2.left_mem_of_mem_openSegment hp1.1 hp2.1 hz1 hop1
  have hp1eq : p1 = (p1.1, q) := Prod.ext rfl hp1q
  rw [hp1eq]
  have : (p1.1, q) ∈ (fun a => (a, q)) '' segment ℝ x y := ⟨p1.1, hp11, rfl⟩
  simpa [Prod.image_mk_segment_left] using this

theorem adj_prod_right {P : Set E} {Q : Set F} {p : E} {x y : F}
    (hp : p ∈ extremePoints ℝ P) (h : Adj Q x y) :
    Adj (P ×ˢ Q) (p, x) (p, y) := by
  have hne : (p, x) ≠ (p, y) := by
    intro hxy
    exact h.1 (Prod.mk.inj hxy).2
  have hpP : p ∈ P := extremePoints_subset hp
  have hsubset : segment ℝ (p, x) (p, y) ⊆ P ×ˢ Q := by
    intro z hz
    have hz' : z ∈ (fun b => (p, b)) '' segment ℝ x y := by
      simpa [Prod.image_mk_segment_right] using hz
    obtain ⟨b, hb, rfl⟩ := hz'
    exact ⟨hpP, h.2.1 hb⟩
  refine ⟨hne, hsubset, ?_⟩
  intro p1 hp1 p2 hp2 z hz hzopen
  have hz1 : z.1 = p := by
    have hz' : z ∈ (fun b => (p, b)) '' segment ℝ x y := by
      simpa [Prod.image_mk_segment_right] using hz
    obtain ⟨b, hb, rfl⟩ := hz'
    rfl
  obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hzopen
  have h1 : α • p1.1 + β • p2.1 = p := by
    have := congrArg Prod.fst hcomb
    simpa [hz1] using this
  have hop1 : p ∈ openSegment ℝ p1.1 p2.1 := ⟨α, β, hα, hβ, hαβ, h1⟩
  have hp11 : p1.1 = p := hp.2 hp1.1 hp2.1 hop1
  have hp21 : p2.1 = p := by
    have hop1' : p ∈ openSegment ℝ p2.1 p1.1 := by
      simpa [openSegment_symm] using hop1
    exact hp.2 hp2.1 hp1.1 hop1'
  have hz2 : z.2 ∈ segment ℝ x y := by
    have hz' : z ∈ (fun b => (p, b)) '' segment ℝ x y := by
      simpa [Prod.image_mk_segment_right] using hz
    obtain ⟨b, hb, hza⟩ := hz'
    have : z.2 = b := by
      have := congrArg Prod.snd hza
      exact this.symm
    simpa [this] using hb
  have hop2 : z.2 ∈ openSegment ℝ p1.2 p2.2 := by
    refine ⟨α, β, hα, hβ, hαβ, ?_⟩
    have := congrArg Prod.snd hcomb
    simpa using this
  have hp12 : p1.2 ∈ segment ℝ x y :=
    h.2.left_mem_of_mem_openSegment hp1.2 hp2.2 hz2 hop2
  have hp1eq : p1 = (p, p1.2) := Prod.ext hp11 rfl
  rw [hp1eq]
  have : (p, p1.2) ∈ (fun b => (p, b)) '' segment ℝ x y := ⟨p1.2, hp12, rfl⟩
  simpa [Prod.image_mk_segment_right] using this

theorem solution
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (P : Set E) (Q : Set F) (B C : ℕ)
    (hP : DiamLE P B) (hQ : DiamLE Q C) :
    DiamLE (P ×ˢ Q) (B + C) := by
  intro u hu v hv
  have hu' : u ∈ P.extremePoints ℝ ×ˢ Q.extremePoints ℝ := by
    simpa [extremePoints_prod] using hu
  have hv' : v ∈ P.extremePoints ℝ ×ˢ Q.extremePoints ℝ := by
    simpa [extremePoints_prod] using hv
  obtain ⟨wP, hwP0, hwPB, hsP⟩ := hP u.1 hu'.1 v.1 hv'.1
  obtain ⟨wQ, hwQ0, hwQC, hsQ⟩ := hQ u.2 hu'.2 v.2 hv'.2
  let w : ℕ → E × F := fun t =>
    if t ≤ B then (wP t, u.2) else (v.1, wQ (t - B))
  refine ⟨w, ?_, ?_, ?_⟩
  · simp [w, hwP0]
  · by_cases hC : C = 0
    · have hB : B + C = B := by simp [hC]
      have hv2 : u.2 = v.2 := by
        have hwQend : wQ 0 = v.2 := by simpa [hC] using hwQC
        exact hwQ0.symm.trans hwQend
      simp [w, hB, hwPB, hv2]
    · have hle : ¬ (B + C ≤ B) := by omega
      have hsub : B + C - B = C := Nat.add_sub_cancel_left B C
      simp [w, hle, hsub, hwQC]
  · intro t ht
    by_cases htB : t < B
    · have ht' : t ≤ B := Nat.le_of_lt htB
      have ht1 : t + 1 ≤ B := Nat.succ_le_of_lt htB
      have hwt : w t = (wP t, u.2) := if_pos ht'
      have hwt1 : w (t + 1) = (wP (t + 1), u.2) := if_pos ht1
      rcases hsP t htB with hstat | hadj
      · exact Or.inl (by simp [hwt, hwt1, hstat])
      · refine Or.inr ?_
        simpa [hwt, hwt1] using adj_prod_left hu'.2 hadj
    · have htge : B ≤ t := Nat.le_of_not_gt htB
      have hwt : w t = (v.1, wQ (t - B)) := by
        by_cases hteq : t ≤ B
        · have htEq : t = B := le_antisymm hteq htge
          subst t
          simp [w, hwPB, hwQ0]
        · simp [w, hteq]
      have hwt1 : w (t + 1) = (v.1, wQ (t + 1 - B)) := by
        have : ¬ (t + 1 ≤ B) := by omega
        simp [w, this]
      have hidx : t + 1 - B = (t - B) + 1 := by omega
      have htQ : t - B < C := by omega
      rcases hsQ (t - B) htQ with hstat | hadj
      · exact Or.inl (by simp [hwt, hwt1, hidx, hstat])
      · refine Or.inr ?_
        have hadj' := adj_prod_right hv'.1 hadj
        simpa [hwt, hwt1, hidx] using hadj'

#print axioms solution
