-- Prove2me | solution 1 for VLF.vlDist_triangle
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:49:53.192275+00:00
-- url     : https://prove2.me/submissions/2d708094-2aa9-4e6e-acea-4e755ecdd914

-- Sol generated from Bridges/VoiceLeadingFunctor.lean
import Mathlib
import Definitions.Def_Bridges_VoiceLeadingFunctor

/-!
# Voice-Leading as a Category with Functor to Lawvere Metric Spaces

This file constructs a **category** whose objects are equal-cardinality voicings
and whose morphisms are voice-leadings (permutation-based assignments), then
proves the fundamental **cost triangle inequality** that makes it a Lawvere metric.

## Main Results

* `VLF.VLHom.cost_comp_le` — Triangle inequality for composition of voice-leadings
* `VLF.VLHom.cost_id` — Identity morphism has zero cost
* `VLF.vlBundledLawvere` — Voice-leadings form a Lawvere metric space
* `VLF.vlDist_triangle` — Triangle inequality for minimum voice-leading distance

## Mathematical Significance

Voice-leading — the art of moving smoothly between chords — is shown to be
not merely a musical heuristic but a **functorial distance theory**: the cost
of voice-leading satisfies the enriched composition law of Lawvere metric spaces.
-/

open Finset BigOperators CategoryTheory

noncomputable section

open VLF

/-! ## Core Definitions -/








/-
**Triangle inequality for voice-leading cost**: the cost of a composed
voice-leading is at most the sum of the individual costs.
This is the fundamental enriched composition law.
-/

/-! ## Minimum Voice-Leading Distance -/




/-
Triangle inequality for minimum voice-leading distance.
-/

/-! ## Lawvere Metric Space -/



/-! ## Bridge: Cost as Categorical Distance -/




open VLF in
theorem solution{n : ℕ} (V W U : Voicing n) :
    vlDist V U ≤ vlDist V W + vlDist W U := by
  -- Apply the triangle inequality to each term in the infimum.
  have h_triangle : ∀ σ₁ σ₂ : Equiv.Perm (Fin n), (∑ i : Fin n, |(V i : ℝ) - (U (σ₁.trans σ₂ i) : ℝ)|) ≤ (∑ i : Fin n, |(V i : ℝ) - (W (σ₁ i) : ℝ)|) + (∑ i : Fin n, |(W i : ℝ) - (U (σ₂ i) : ℝ)|) := by
    intros σ₁ σ₂
    have h_triangle : ∀ i : Fin n, |(V i : ℝ) - (U (σ₁.trans σ₂ i) : ℝ)| ≤ |(V i : ℝ) - (W (σ₁ i) : ℝ)| + |(W (σ₁ i) : ℝ) - (U (σ₁.trans σ₂ i) : ℝ)| := by
      exact fun i => abs_sub_le _ _ _;
    convert Finset.sum_le_sum fun i _ => h_triangle i using 1;
    simp +decide [ Finset.sum_add_distrib, Equiv.sum_comp σ₁ fun i => |( W i : ℝ ) - U ( σ₂ i )| ];
  -- By definition of infimum, for any ε > 0, there exist permutations σ₁ and σ₂ such that the sum of the costs of the individual voice-leadings is within ε of the infimum.
  have h_inf : ∀ ε > 0, ∃ σ₁ σ₂ : Equiv.Perm (Fin n), (∑ i : Fin n, |(V i : ℝ) - (W (σ₁ i) : ℝ)|) < vlDist V W + ε ∧ (∑ i : Fin n, |(W i : ℝ) - (U (σ₂ i) : ℝ)|) < vlDist W U + ε := by
    intro ε hε
    have h_inf_VW : ∃ σ₁ : Equiv.Perm (Fin n), (∑ i : Fin n, |(V i : ℝ) - (W (σ₁ i) : ℝ)|) < vlDist V W + ε := by
      have := Finset.exists_min_image Finset.univ ( fun σ : Equiv.Perm ( Fin n ) => ∑ i : Fin n, |( V i : ℝ ) - W ( σ i )| ) ⟨ Equiv.refl ( Fin n ), Finset.mem_univ _ ⟩;
      exact ⟨ this.choose, lt_of_le_of_lt ( this.choose_spec.2 _ ( Finset.mem_univ _ ) ) ( lt_add_of_le_of_pos ( Finset.le_inf' _ _ fun x hx => this.choose_spec.2 x hx ) hε ) ⟩
    have h_inf_WU : ∃ σ₂ : Equiv.Perm (Fin n), (∑ i : Fin n, |(W i : ℝ) - (U (σ₂ i) : ℝ)|) < vlDist W U + ε := by
      contrapose! hε;
      exact le_of_not_gt fun h => by have := Finset.exists_min_image Finset.univ ( fun σ₂ : Equiv.Perm ( Fin n ) => ∑ i : Fin n, |( W i : ℝ ) - U ( σ₂ i )| ) ⟨ Equiv.refl _, Finset.mem_univ _ ⟩ ; obtain ⟨ σ₂, hσ₂₁, hσ₂₂ ⟩ := this; linarith [ hε σ₂, show vlDist W U = ∑ i : Fin n, |( W i : ℝ ) - U ( σ₂ i )| from le_antisymm ( Finset.inf'_le _ <| Finset.mem_univ _ ) <| Finset.le_inf' _ _ fun σ₃ hσ₃ => hσ₂₂ σ₃ <| Finset.mem_univ _ ] ;
    obtain ⟨σ₁, hσ₁⟩ := h_inf_VW
    obtain ⟨σ₂, hσ₂⟩ := h_inf_WU
    use σ₁, σ₂;
  refine' le_of_forall_pos_le_add fun ε ε_pos => _;
  obtain ⟨ σ₁, σ₂, h₁, h₂ ⟩ := h_inf ( ε / 2 ) ( half_pos ε_pos ) ; exact le_trans ( Finset.inf'_le _ ( Finset.mem_univ ( σ₁.trans σ₂ ) ) ) ( by linarith [ h_triangle σ₁ σ₂ ] ) ;
