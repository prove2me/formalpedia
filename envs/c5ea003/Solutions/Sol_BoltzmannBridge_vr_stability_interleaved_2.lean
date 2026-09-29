-- Prove2me | solution 2 for BoltzmannBridge.vr_stability_interleaved
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:31:36.408993+00:00
-- url     : https://prove2.me/submissions/3d300fef-338b-4918-9baf-67d018553a46

import Mathlib
import Definitions.Def_Applications_BoltzmannBridge_BottleneckStability
import Definitions.Def_Applications_BoltzmannBridge_HigherPersistence
open Finset BigOperators BoltzmannBridge BoltzmannBridge.Filtration in
theorem solution {α : Type*} (d₁ d₂ : α → α → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ x y, |d₁ x y - d₂ x y| ≤ ε) :
    Filtration.Interleaved (diamFiltrationOf d₁) (diamFiltrationOf d₂) ε := by
  -- the diameter weight is `1`-Lipschitz in the dissimilarity
  have key : ∀ (e₁ e₂ : α → α → ℝ), (∀ x y, e₁ x y ≤ e₂ x y + ε) →
      ∀ σ : Finset α, diamWeightOf e₁ σ ≤ diamWeightOf e₂ σ + ε := by
    intro e₁ e₂ he σ
    unfold diamWeightOf
    have h0 : id (0 : ℝ) ≤ (insert (0 : ℝ) ((σ ×ˢ σ).image (fun p => e₂ p.1 p.2))).sup'
        (insert_nonempty _ _) id :=
      le_sup' id (mem_insert_self 0 _)
    refine sup'_le _ _ (fun b hb => ?_)
    rcases mem_insert.1 hb with rfl | hb
    · simp only [id] at h0 ⊢
      linarith
    · obtain ⟨p, hp, rfl⟩ := mem_image.1 hb
      have h1 := le_sup' id (mem_insert_of_mem (mem_image_of_mem (fun p => e₂ p.1 p.2) hp)
        : e₂ p.1 p.2 ∈ insert (0 : ℝ) ((σ ×ˢ σ).image (fun p => e₂ p.1 p.2)))
      simp only [id] at h1 ⊢
      linarith [he p.1 p.2]
  refine ⟨hε, fun t σ hσ => ?_, fun t σ hσ => ?_⟩
  · have hw : diamWeightOf d₁ σ ≤ t := hσ
    have := key d₂ d₁ (fun x y => by linarith [(abs_le.1 (h x y)).1]) σ
    show diamWeightOf d₂ σ ≤ t + ε
    linarith
  · have hw : diamWeightOf d₂ σ ≤ t := hσ
    have := key d₁ d₂ (fun x y => by linarith [(abs_le.1 (h x y)).2]) σ
    show diamWeightOf d₁ σ ≤ t + ε
    linarith
