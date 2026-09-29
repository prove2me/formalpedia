-- Prove2me | Definitions.Def_Bridges_VoiceLeadingCategory
-- name    : Bridges_VoiceLeadingCategory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:46:49.249123+00:00
-- url     : https://prove2.me/theorems/e4ada859-e7eb-4516-8f43-847f09ae5d8d
-- title:
--   Aether Catalog definitions — Bridges_VoiceLeadingCategory
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.VoiceLeadingCategory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/VoiceLeadingCategory.lean by skeleton subtraction
import Mathlib

/-!
# Categorical Voice-Leading Geometry

This file defines a category of voice-leadings between equal-cardinality pitch-class
configurations and proves that voice-leading cost satisfies the triangle inequality,
making it a functor into Lawvere metric spaces (enriched categories over [0,∞]).

## Main Results

* `VoiceLeading.cost_id` — Identity voice-leading has zero cost
* `voiceLeading_cost_comp_le` — **Triangle inequality**: cost of composition ≤ sum of costs
* `vlDist_triangle` — Triangle inequality for minimum voice-leading distance
* `vlLawvere` — Voice-leadings form a Lawvere metric space

## Mathematical Significance

Voice-leading — the art of moving smoothly between chords — is shown to be
not merely a musical heuristic but a **functorial distance theory**. The cost
of a voice-leading (sum of pitch displacements) satisfies the enriched
composition law of a Lawvere metric space. This creates a formal bridge between
music theory, enriched category theory, and optimal transport.
-/

open Finset BigOperators CategoryTheory

noncomputable section

namespace VoiceLeading

/-! ## Core Definitions -/

/-- A voicing of `n` notes is a function from `Fin n` to pitch classes in ℤ. -/
def Voicing (n : ℕ) := Fin n → ℤ

instance (n : ℕ) : Inhabited (Voicing n) := ⟨fun _ => 0⟩

/-- A voice-leading between two voicings of the same cardinality:
    an assignment of each voice in the source to a voice in the target,
    given by a permutation of voice indices. -/
structure VL (n : ℕ) (V W : Voicing n) where
  /-- The voice assignment permutation -/
  perm : Equiv.Perm (Fin n)

/-- The cost (total displacement) of a voice-leading:
    the sum of absolute pitch differences under the assignment. -/
def VL.cost {n : ℕ} {V W : Voicing n} (f : VL n V W) : ℝ :=
  ∑ i : Fin n, |(V i : ℝ) - (W (f.perm i) : ℝ)|

/-- The identity voice-leading: each voice maps to itself. -/
def VL.id {n : ℕ} (V : Voicing n) : VL n V V where
  perm := Equiv.refl _

/-- Composition of voice-leadings: if f maps voice i to f.perm(i) and g maps voice j to g.perm(j),
    then f;g maps voice i to g.perm(f.perm(i)). -/
def VL.comp {n : ℕ} {V W U : Voicing n} (f : VL n V W) (g : VL n W U) : VL n V U where
  perm := f.perm.trans g.perm

/-! ## Cost Properties -/






/-! ## Minimum Voice-Leading Distance -/

/-- The minimum voice-leading distance between two voicings:
    the infimum of cost over all possible voice assignments.
    Uses `Finset.inf'` over all permutations. -/
def vlDist {n : ℕ} (V W : Voicing n) : ℝ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).inf'
    (Finset.univ_nonempty)
    (fun σ => ∑ i : Fin n, |(V i : ℝ) - (W (σ i) : ℝ)|)

/-
Minimum voice-leading distance is nonneg.
-/
theorem vlDist_nonneg {n : ℕ} (V W : Voicing n) : 0 ≤ vlDist V W := by
  exact Finset.le_inf' _ _ fun σ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

/-
Minimum voice-leading distance from a voicing to itself is zero.
-/
theorem vlDist_self {n : ℕ} (V : Voicing n) : vlDist V V = 0 := by
  refine' le_antisymm ( Finset.inf'_le _ ( Finset.mem_univ ( Equiv.refl ( Fin n ) ) ) |> le_trans <| _ ) ( vlDist_nonneg _ _ );
  norm_num

/-
**Triangle inequality for minimum voice-leading distance**:
    vlDist(V, U) ≤ vlDist(V, W) + vlDist(W, U)
-/
theorem vlDist_triangle {n : ℕ} (V W U : Voicing n) :
    vlDist V U ≤ vlDist V W + vlDist W U := by
  -- Let σ₁ achieve vlDist(V,W), let σ₂ achieve vlDist(W,U).
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : Equiv.Perm (Fin n), vlDist V W = ∑ i : Fin n, |(V i : ℝ) - (W (σ₁ i) : ℝ)| := by
    have h_inf : ∃ σ : Equiv.Perm (Fin n), ∀ τ : Equiv.Perm (Fin n), ∑ i : Fin n, |(V i : ℝ) - (W (τ i) : ℝ)| ≥ ∑ i : Fin n, |(V i : ℝ) - (W (σ i) : ℝ)| := by
      simpa using Finset.exists_min_image Finset.univ ( fun τ : Equiv.Perm ( Fin n ) => ∑ i : Fin n, |( V i : ℝ ) - W ( τ i )| ) ⟨ Equiv.refl _, Finset.mem_univ _ ⟩;
    exact ⟨ h_inf.choose, le_antisymm ( Finset.inf'_le _ <| Finset.mem_univ _ ) <| Finset.le_inf' _ _ fun τ hτ => h_inf.choose_spec τ ⟩
  obtain ⟨σ₂, hσ₂⟩ : ∃ σ₂ : Equiv.Perm (Fin n), vlDist W U = ∑ i : Fin n, |(W i : ℝ) - (U (σ₂ i) : ℝ)| := by
    have := Finset.exists_min_image Finset.univ ( fun σ : Equiv.Perm ( Fin n ) => ∑ i : Fin n, |( W i : ℝ ) - ( U ( σ i ) : ℝ )| ) ⟨ Equiv.refl _, Finset.mem_univ _ ⟩;
    obtain ⟨ σ₂, hσ₂₁, hσ₂₂ ⟩ := this; exact ⟨ σ₂, le_antisymm ( Finset.inf'_le _ <| Finset.mem_univ _ ) <| Finset.le_inf' _ _ fun x hx => hσ₂₂ x <| Finset.mem_univ _ ⟩ ;
  -- Apply the triangle inequality to the composed permutation σ₁.trans σ₂.
  have h_triangle : ∑ i : Fin n, |(V i : ℝ) - (U ((σ₁.trans σ₂) i) : ℝ)| ≤ ∑ i : Fin n, |(V i : ℝ) - (W (σ₁ i) : ℝ)| + ∑ i : Fin n, |(W (σ₁ i) : ℝ) - (U ((σ₁.trans σ₂) i) : ℝ)| := by
    simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_le_sum fun i _ => abs_sub_le _ _ _;
  refine' le_trans _ ( h_triangle.trans_eq _ );
  · exact Finset.inf'_le _ ( Finset.mem_univ _ );
  · simp +decide [ ← hσ₁, ← hσ₂, Equiv.sum_comp σ₁ fun i => |( W i : ℝ ) - ( U ( σ₂ i ) : ℝ )| ]

/-! ## Lawvere Metric Category -/

/-- A Lawvere metric space: a type with a distance function satisfying
    d(x,x) = 0 and d(x,z) ≤ d(x,y) + d(y,z).
    Note: unlike a metric space, we do not require symmetry or separation. -/
class LawvereMetric (X : Type*) where
  dist : X → X → ℝ
  dist_self : ∀ x, dist x x = 0
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  dist_triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

/-- Voice-leadings form a Lawvere metric space under minimum voice-leading distance. -/
instance vlLawvere (n : ℕ) : LawvereMetric (Voicing n) where
  dist := vlDist
  dist_self := vlDist_self
  dist_nonneg := vlDist_nonneg
  dist_triangle := vlDist_triangle

/-! ## Bridge to Rate-Distortion -/


end VoiceLeading


