-- Prove2me | solution 1 for sheaf_per_chart_lipschitz_radius
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T03:19:22.582392+00:00
-- url     : https://prove2.me/submissions/864c8830-0f72-40f9-9f34-c7efa4a17cd2

import Mathlib
import Definitions.Def_MachineLearning_NeuralCoding_CechDecisionBoundaryObstructions

open Finset Set in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : Type*} [PseudoMetricSpace X]
    (scoreGap : X → ℝ) (S : Set X)
    (cover : ι → Set X)
    (D : LocalLipschitzData ι)
    (hcover : S ⊆ ⋃ i, cover i)
    (hmargin : ∀ i, ∀ x ∈ cover i, D.margin i ≤ scoreGap x)
    (hlip : ∀ i, ∀ x ∈ cover i, ∀ y : X,
      |scoreGap x - scoreGap y| ≤ D.lipschitz i * dist x y)
    (_hH1 : VanishingH1OnCover ι) :
    ∃ r : ℝ, 0 < r ∧
      Finset.inf' Finset.univ Finset.univ_nonempty D.localRadius ≤ r ∧
      CertifiedRobustRadiusLinf scoreGap S r := by
  -- the smallest local radius already certifies every chart
  set ρ := Finset.inf' Finset.univ Finset.univ_nonempty D.localRadius with hρ
  have hρpos : 0 < ρ := by
    rw [hρ, Finset.lt_inf'_iff]
    intro i _
    exact div_pos (D.margin_pos i) (D.lipschitz_pos i)
  refine ⟨ρ, hρpos, le_rfl, ⟨hρpos, fun x hx y hy => ?_⟩⟩
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcover hx)
  have hle : ρ ≤ D.localRadius i := Finset.inf'_le _ (Finset.mem_univ i)
  have hL := D.lipschitz_pos i
  have hd : D.lipschitz i * dist x y < D.margin i := by
    rw [dist_comm]
    have h0 : dist y x < D.margin i / D.lipschitz i := lt_of_lt_of_le hy hle
    rwa [lt_div_iff₀ hL, mul_comm] at h0
  have h1 := (abs_le.1 (hlip i x hi y)).2
  have h2 := hmargin i x hi
  linarith
