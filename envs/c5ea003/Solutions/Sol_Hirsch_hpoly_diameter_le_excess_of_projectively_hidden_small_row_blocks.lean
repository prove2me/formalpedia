-- Prove2me | solution 1 for Hirsch.hpoly_diameter_le_excess_of_projectively_hidden_small_row_blocks
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T18:29:19.715739+00:00
-- url     : https://prove2.me/submissions/84cf11d7-d965-41c3-96b6-d0f108e8ce2e

import Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_independent_small_row_blocks
import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch


/-!
# Segment-chart transport of the ordinary vertex-edge graph

A chart need only be injective on a convex domain; it need not be affine or
injective on the entire ambient vector space. This is the transport primitive
for a positive-denominator projective chart. Verification receipts are kept
separately from this mathematical source.
-/
open Set
set_option autoImplicit false
noncomputable section

namespace Hirsch

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

/-- A segment-preserving embedding of a convex domain. Both image identities
are required: an arbitrary nonlinear injection is insufficient for edge transport. -/
structure SegmentChart (U : Set E) (f : E → F) : Prop where
  convex : Convex ℝ U
  injOn : Set.InjOn f U
  segment_image : ∀ x ∈ U, ∀ y ∈ U,
    f '' segment ℝ x y = segment ℝ (f x) (f y)
  openSegment_image : ∀ x ∈ U, ∀ y ∈ U,
    f '' openSegment ℝ x y = openSegment ℝ (f x) (f y)

namespace SegmentChart

variable {U : Set E} {f : E → F} (h : SegmentChart U f)
include h

/-- Preserve and reflect extreme subsets without assuming a global inverse. -/
theorem isExtreme_image_iff {P C : Set E}
    (hP : P ⊆ U) (hC : C ⊆ U) :
    IsExtreme ℝ (f '' P) (f '' C) ↔ IsExtreme ℝ P C := by
  constructor
  · intro he
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨x, hx, hxf⟩ := he.1 ⟨z, hz, rfl⟩
      have hxz := h.injOn (hP hx) (hC hz) hxf
      simpa [hxz] using hx
    · intro x hx y hy z hz hseg
      have hfseg : f z ∈ openSegment ℝ (f x) (f y) := by
        rw [← h.openSegment_image x (hP hx) y (hP hy)]
        exact ⟨z, hseg, rfl⟩
      obtain ⟨t, ht, htf⟩ := he.left_mem_of_mem_openSegment
        ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩ hfseg
      have htx := h.injOn (hC ht) (hP hx) htf
      simpa [htx] using ht
  · intro he
    refine ⟨?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact ⟨z, he.1 hz, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hseg
      rw [← h.openSegment_image x (hP hx) y (hP hy)] at hseg
      obtain ⟨t, ht, htf⟩ := hseg
      have htU : t ∈ U := h.convex.segment_subset (hP hx) (hP hy)
        (openSegment_subset_segment ℝ x y ht)
      have htz := h.injOn htU (hC hz) htf
      subst t
      exact ⟨x, he.left_mem_of_mem_openSegment hx hy hz ht, rfl⟩

/-- A segment chart carries exactly the parent vertices to image vertices. -/
theorem image_extremePoints (P : Set E) (hP : P ⊆ U) :
    f '' extremePoints ℝ P = extremePoints ℝ (f '' P) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxU : ({x} : Set E) ⊆ U := by
      intro z hz
      simpa only [Set.mem_singleton_iff.mp hz] using hP hx.1
    have he := (h.isExtreme_image_iff hP hxU).2 (isExtreme_singleton.mpr hx)
    exact isExtreme_singleton.mp (by simpa using he)
  · intro y hy
    obtain ⟨x, hxP, rfl⟩ := hy.1
    have hxU : ({x} : Set E) ⊆ U := by
      intro z hz
      simpa only [Set.mem_singleton_iff.mp hz] using hP hxP
    have he : IsExtreme ℝ (f '' P) (f '' ({x} : Set E)) := by
      simpa using isExtreme_singleton.mpr hy
    exact ⟨x, isExtreme_singleton.mp ((h.isExtreme_image_iff hP hxU).1 he), rfl⟩

/-- Ordinary adjacency, not circuit adjacency, is invariant on the chart. -/
theorem adj_iff (P : Set E) (hP : P ⊆ U)
    (x y : E) (hx : x ∈ U) (hy : y ∈ U) :
    Adj (f '' P) (f x) (f y) ↔ Adj P x y := by
  have hS : segment ℝ x y ⊆ U := h.convex.segment_subset hx hy
  have hface := h.isExtreme_image_iff hP hS
  rw [h.segment_image x hx y hy] at hface
  constructor
  · rintro ⟨hne, he⟩
    exact ⟨fun hxy => hne (congrArg f hxy), hface.mp he⟩
  · rintro ⟨hne, he⟩
    exact ⟨fun hfxy => hne (h.injOn hx hy hfxy), hface.mpr he⟩

/-- The same padded number of ordinary edges works in the image. -/
theorem diamLE_image (P : Set E) (hP : P ⊆ U) (B : ℕ)
    (hdiam : DiamLE P B) : DiamLE (f '' P) B := by
  intro u hu v hv
  rw [← h.image_extremePoints P hP] at hu hv
  obtain ⟨x, hx, rfl⟩ := hu
  obtain ⟨y, hy, rfl⟩ := hv
  obtain ⟨w, hw0, hwB, hs⟩ := hdiam x hx y hy
  refine ⟨fun i => f (w i), by simp [hw0], by simp [hwB], ?_⟩
  intro i hi
  rcases hs i hi with heq | hadj
  · exact Or.inl (congrArg f heq)
  · have hxP : w i ∈ P := hadj.2.1 (left_mem_segment ℝ _ _)
    have hyP : w (i + 1) ∈ P := hadj.2.1 (right_mem_segment ℝ _ _)
    exact Or.inr ((h.adj_iff P hP _ _ (hP hxP) (hP hyP)).2 hadj)

end SegmentChart

#print axioms SegmentChart.isExtreme_image_iff
#print axioms SegmentChart.image_extremePoints
#print axioms SegmentChart.adj_iff
#print axioms SegmentChart.diamLE_image
end Hirsch

end

/-!
# Positive projective charts preserve the ordinary edge graph

The map x |-> x / (1 + l(x)) has inverse y |-> y / (1 - l(y)) on the
respective positive-denominator domains. Explicit segment reweighting, not an
assumed projective-invariance axiom, supplies the transport certificate.
The kernel and axiom verification receipts are maintained separately.
-/
open Set
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschPerspective

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def denominator (l : E →ₗ[ℝ] ℝ) (x : E) : ℝ := 1 + l x

def perspective (l : E →ₗ[ℝ] ℝ) (x : E) : E :=
  (denominator l x)⁻¹ • x

def positiveDomain (l : E →ₗ[ℝ] ℝ) : Set E :=
  {x | 0 < denominator l x}

lemma denominator_mix (l : E →ₗ[ℝ] ℝ) (x y : E) (a b : ℝ)
    (hab : a + b = 1) :
    denominator l (a • x + b • y) = a * denominator l x + b * denominator l y := by
  simp only [denominator, map_add, map_smul, smul_eq_mul]
  nlinarith

private lemma weighted_pos {a b s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hs : 0 < s) (ht : 0 < t) : 0 < a*s + b*t := by
  rcases eq_or_lt_of_le ha with hzero | hpos
  · have ha0 : a = 0 := hzero.symm
    have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using ht
  · exact add_pos_of_pos_of_nonneg (mul_pos hpos hs) (mul_nonneg hb ht.le)

lemma positiveDomain_convex (l : E →ₗ[ℝ] ℝ) : Convex ℝ (positiveDomain l) := by
  intro x hx y hy a b ha hb hab
  change 0 < denominator l (a • x + b • y)
  rw [denominator_mix l x y a b hab]
  exact weighted_pos ha hb hab hx hy

lemma denominator_neg_perspective (l : E →ₗ[ℝ] ℝ) (x : E)
    (hx : denominator l x ≠ 0) :
    denominator (-l) (perspective l x) = (denominator l x)⁻¹ := by
  have hx' : 1 + l x ≠ 0 := hx
  simp only [denominator, perspective, LinearMap.neg_apply, map_smul, smul_eq_mul]
  field_simp [hx']
  ring

lemma perspective_inverse (l : E →ₗ[ℝ] ℝ) (x : E)
    (hx : denominator l x ≠ 0) :
    perspective (-l) (perspective l x) = x := by
  change (denominator (-l) (perspective l x))⁻¹ •
    ((denominator l x)⁻¹ • x) = x
  rw [denominator_neg_perspective l x hx, inv_inv, smul_smul,
    mul_inv_cancel₀ hx, one_smul]

lemma perspective_mem_opposite_domain (l : E →ₗ[ℝ] ℝ) {x : E}
    (hx : x ∈ positiveDomain l) : perspective l x ∈ positiveDomain (-l) := by
  change 0 < denominator (-l) (perspective l x)
  rw [denominator_neg_perspective l x (ne_of_gt hx)]
  exact inv_pos.mpr hx

lemma perspective_injOn (l : E →ₗ[ℝ] ℝ) :
    Set.InjOn (perspective l) (positiveDomain l) := by
  intro x hx y hy he
  have hback := congrArg (perspective (-l)) he
  rwa [perspective_inverse l x (ne_of_gt hx),
    perspective_inverse l y (ne_of_gt hy)] at hback

/-- Explicit reweighting identity. Positivity is handled in the segment lemmas. -/
lemma perspective_mix (l : E →ₗ[ℝ] ℝ) (x y : E) (a b : ℝ)
    (hx : denominator l x ≠ 0) (hy : denominator l y ≠ 0)
    (hz : denominator l (a • x + b • y) ≠ 0) :
    perspective l (a • x + b • y) =
      (a * denominator l x / denominator l (a • x + b • y)) • perspective l x +
      (b * denominator l y / denominator l (a • x + b • y)) • perspective l y := by
  simp only [perspective, smul_add, smul_smul]
  congr 1
  · congr 1
    field_simp [hx, hz]
  · congr 1
    field_simp [hy, hz]

lemma perspective_mem_segment (l : E →ₗ[ℝ] ℝ) {x y z : E}
    (hx : x ∈ positiveDomain l) (hy : y ∈ positiveDomain l)
    (hz : z ∈ segment ℝ x y) :
    perspective l z ∈ segment ℝ (perspective l x) (perspective l y) := by
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  have hd : 0 < denominator l (a • x + b • y) := by
    rw [denominator_mix l x y a b hab]
    exact weighted_pos ha hb hab hx hy
  refine ⟨a * denominator l x / denominator l (a • x + b • y),
    b * denominator l y / denominator l (a • x + b • y),
    div_nonneg (mul_nonneg ha (le_of_lt hx)) hd.le,
    div_nonneg (mul_nonneg hb (le_of_lt hy)) hd.le, ?_, ?_⟩
  · rw [← add_div, ← denominator_mix l x y a b hab, div_self (ne_of_gt hd)]
  · exact (perspective_mix l x y a b (ne_of_gt hx) (ne_of_gt hy) (ne_of_gt hd)).symm

lemma perspective_mem_openSegment (l : E →ₗ[ℝ] ℝ) {x y z : E}
    (hx : x ∈ positiveDomain l) (hy : y ∈ positiveDomain l)
    (hz : z ∈ openSegment ℝ x y) :
    perspective l z ∈ openSegment ℝ (perspective l x) (perspective l y) := by
  rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
  have hd : 0 < denominator l (a • x + b • y) := by
    rw [denominator_mix l x y a b hab]
    exact weighted_pos ha.le hb.le hab hx hy
  refine ⟨a * denominator l x / denominator l (a • x + b • y),
    b * denominator l y / denominator l (a • x + b • y),
    div_pos (mul_pos ha hx) hd, div_pos (mul_pos hb hy) hd, ?_, ?_⟩
  · rw [← add_div, ← denominator_mix l x y a b hab, div_self (ne_of_gt hd)]
  · exact (perspective_mix l x y a b (ne_of_gt hx) (ne_of_gt hy) (ne_of_gt hd)).symm

lemma perspective_image_segment (l : E →ₗ[ℝ] ℝ) {x y : E}
    (hx : x ∈ positiveDomain l) (hy : y ∈ positiveDomain l) :
    perspective l '' segment ℝ x y =
      segment ℝ (perspective l x) (perspective l y) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact perspective_mem_segment l hx hy hz
  · intro z hz
    have hx' := perspective_mem_opposite_domain l hx
    have hy' := perspective_mem_opposite_domain l hy
    have hz' : z ∈ positiveDomain (-l) :=
      (positiveDomain_convex (-l)).segment_subset hx' hy' hz
    have hpre := perspective_mem_segment (-l) hx' hy' hz
    rw [perspective_inverse l x (ne_of_gt hx),
      perspective_inverse l y (ne_of_gt hy)] at hpre
    refine ⟨perspective (-l) z, hpre, ?_⟩
    simpa only [neg_neg] using perspective_inverse (-l) z (ne_of_gt hz')

lemma perspective_image_openSegment (l : E →ₗ[ℝ] ℝ) {x y : E}
    (hx : x ∈ positiveDomain l) (hy : y ∈ positiveDomain l) :
    perspective l '' openSegment ℝ x y =
      openSegment ℝ (perspective l x) (perspective l y) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact perspective_mem_openSegment l hx hy hz
  · intro z hz
    have hx' := perspective_mem_opposite_domain l hx
    have hy' := perspective_mem_opposite_domain l hy
    have hz' : z ∈ positiveDomain (-l) :=
      (positiveDomain_convex (-l)).segment_subset hx' hy'
        (openSegment_subset_segment ℝ _ _ hz)
    have hpre := perspective_mem_openSegment (-l) hx' hy' hz
    rw [perspective_inverse l x (ne_of_gt hx),
      perspective_inverse l y (ne_of_gt hy)] at hpre
    refine ⟨perspective (-l) z, hpre, ?_⟩
    simpa only [neg_neg] using perspective_inverse (-l) z (ne_of_gt hz')

/-- The projective chart, with all segment identities proved explicitly. -/
theorem perspective_segmentChart (l : E →ₗ[ℝ] ℝ) :
    Hirsch.SegmentChart (positiveDomain l) (perspective l) := by
  refine ⟨positiveDomain_convex l, perspective_injOn l, ?_, ?_⟩
  · intro x hx y hy
    exact perspective_image_segment l hx hy
  · intro x hx y hy
    exact perspective_image_openSegment l hx hy

/-- Every ordinary-edge diameter bound transports at exactly the same budget. -/
theorem perspective_diamLE_image (l : E →ₗ[ℝ] ℝ) (P : Set E)
    (hP : P ⊆ positiveDomain l) (B : ℕ) (hdiam : Hirsch.DiamLE P B) :
    Hirsch.DiamLE (perspective l '' P) B :=
  (perspective_segmentChart l).diamLE_image P hP B hdiam

#print axioms denominator_neg_perspective
#print axioms perspective_inverse
#print axioms perspective_mix
#print axioms perspective_segmentChart
#print axioms perspective_diamLE_image
end HirschPerspective

end

/-!
# Routing products hidden by a positive projective chart

An exact rank-one row shear A_i |-> A_i + b_i*c preserves the graph when
both projective denominators are positive on their feasible sets. This extends
the existing affine row-block criterion to examples with a connected normal
matroid and arbitrarily large shortest-repair support deficit.

All hypotheses are explicit. No claim is made that arbitrary carriers admit
such a chart. Verification receipts are maintained separately.
-/
open Set Hirsch HirschPerspective
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace HirschProjectiveBlocks

variable {d n : ℕ}

def rowFunctional (c : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ where
  toFun x := ⟪c, x⟫
  map_add' x y := by simp [inner_add_right]
  map_smul' r x := by simp [inner_smul_right]

lemma rowFunctional_neg (c : EuclideanSpace ℝ (Fin d)) :
    rowFunctional (-c) = -rowFunctional c := by
  ext x
  simp [rowFunctional, inner_neg_left]

def shearRows (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (c : EuclideanSpace ℝ (Fin d)) :
    Fin n → EuclideanSpace ℝ (Fin d) := fun i => a i + b i • c

lemma shearRows_inverse (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (c : EuclideanSpace ℝ (Fin d)) :
    shearRows (shearRows a b c) b (-c) = a := by
  funext i
  simp [shearRows, smul_neg, add_assoc]

/-- Exact slack scaling. Its positive divisor is essential to feasibility. -/
theorem shear_slack_identity (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (c x : EuclideanSpace ℝ (Fin d))
    (hx : denominator (rowFunctional c) x ≠ 0) (i : Fin n) :
    b i - ⟪shearRows a b c i, perspective (rowFunctional c) x⟫ =
      (b i - ⟪a i, x⟫) / denominator (rowFunctional c) x := by
  have hd : 1 + ⟪c, x⟫ ≠ 0 := hx
  simp [shearRows, perspective, denominator, rowFunctional,
    inner_add_left, inner_smul_left, inner_smul_right, div_eq_mul_inv]
  field_simp [hd]
  ring

lemma perspective_mem_sheared_hpoly (a : Fin n → EuclideanSpace ℝ (Fin d))
    (b : Fin n → ℝ) (c x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Hpoly a b) (hpos : x ∈ positiveDomain (rowFunctional c)) :
    perspective (rowFunctional c) x ∈ Hpoly (shearRows a b c) b := by
  intro i
  have hs : 0 ≤ b i - ⟪shearRows a b c i, perspective (rowFunctional c) x⟫ := by
    rw [shear_slack_identity a b c x (ne_of_gt hpos) i]
    exact div_nonneg (sub_nonneg.mpr (hx i)) (le_of_lt hpos)
  exact sub_nonneg.mp hs

/-- No missing halfspace is silently discarded: source and target positivity
are both supplied. They can be certified by nonnegative row multipliers. -/
theorem perspective_image_hpoly_eq_shear
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d))
    (hsource : Hpoly a b ⊆ positiveDomain (rowFunctional c))
    (htarget : Hpoly (shearRows a b c) b ⊆ positiveDomain (-rowFunctional c)) :
    perspective (rowFunctional c) '' Hpoly a b = Hpoly (shearRows a b c) b := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact perspective_mem_sheared_hpoly a b c x hx (hsource hx)
  · intro y hy
    have hp : y ∈ positiveDomain (rowFunctional (-c)) := by
      rw [rowFunctional_neg]
      exact htarget hy
    have hpre := perspective_mem_sheared_hpoly (shearRows a b c) b (-c) y hy hp
    rw [shearRows_inverse, rowFunctional_neg] at hpre
    refine ⟨perspective (-rowFunctional c) y, hpre, ?_⟩
    simpa only [neg_neg] using
      perspective_inverse (-rowFunctional c) y (ne_of_gt (htarget hy))

/-- Transport an arbitrary known graph bound through a certified row shear. -/
theorem hpoly_diamLE_of_positive_shear
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (B : ℕ)
    (hsource : Hpoly a b ⊆ positiveDomain (rowFunctional c))
    (htarget : Hpoly (shearRows a b c) b ⊆ positiveDomain (-rowFunctional c))
    (hdiam : DiamLE (Hpoly a b) B) :
    DiamLE (Hpoly (shearRows a b c) b) B := by
  have hr := perspective_diamLE_image (rowFunctional c) (Hpoly a b) hsource B hdiam
  rwa [perspective_image_hpoly_eq_shear a b c hsource htarget] at hr

/-- A checkable Farkas-style sufficient certificate for denominator positivity.
The represented normal is -c, and the weighted upper bound is strictly below 1. -/
theorem positiveDomain_of_row_multipliers
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (weights : Fin n → ℝ)
    (hweights : ∀ i, 0 ≤ weights i)
    (hnormal : (∑ i, weights i • a i) = -c)
    (hmargin : (∑ i, weights i * b i) < 1) :
    Hpoly a b ⊆ positiveDomain (rowFunctional c) := by
  intro x hx
  have hsum : (∑ i, weights i * ⟪a i, x⟫) ≤ ∑ i, weights i * b i :=
    Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hx i) (hweights i))
  have heq : (∑ i, weights i * ⟪a i, x⟫) = -⟪c, x⟫ := by
    calc
      (∑ i, weights i * ⟪a i, x⟫) = ⟪∑ i, weights i • a i, x⟫ := by
        simp [sum_inner, inner_smul_left]
      _ = -⟪c, x⟫ := by rw [hnormal]; simp
  rw [heq] at hsum
  change 0 < 1 + ⟪c, x⟫
  linarith

/-- Consume both finite denominator certificates and transport a known bound.
The hypotheses are identities and inequalities in the describing rows, without
quantification over all feasible points or an assumed chart isomorphism. -/
theorem hpoly_diamLE_of_shear_multipliers
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (c : EuclideanSpace ℝ (Fin d)) (weights inverseWeights : Fin n → ℝ)
    (hweights : ∀ i, 0 ≤ weights i)
    (hnormal : (∑ i, weights i • a i) = -c)
    (hmargin : (∑ i, weights i * b i) < 1)
    (hinverseWeights : ∀ i, 0 ≤ inverseWeights i)
    (hinverseNormal : (∑ i, inverseWeights i • (a i + b i • c)) = c)
    (hinverseMargin : (∑ i, inverseWeights i * b i) < 1)
    (B : ℕ) (hdiam : DiamLE (Hpoly a b) B) :
    DiamLE (Hpoly (fun i => a i + b i • c) b) B := by
  have hsource := positiveDomain_of_row_multipliers a b c weights hweights hnormal hmargin
  have htarget : Hpoly (shearRows a b c) b ⊆ positiveDomain (-rowFunctional c) := by
    rw [← rowFunctional_neg]
    exact positiveDomain_of_row_multipliers (shearRows a b c) b (-c) inverseWeights
      hinverseWeights (by simpa only [neg_neg] using hinverseNormal) hinverseMargin
  exact hpoly_diamLE_of_positive_shear a b c B hsource htarget hdiam


end HirschProjectiveBlocks
end

theorem solution
{d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (hcount : ∀ i, dims i ≤ counts i)
    (hsmallcount : ∀ i, counts i ≤ dims i + 3)
    (c : EuclideanSpace ℝ (Fin d)) (weights inverseWeights : Fin n → ℝ)
    (hweights : ∀ i, 0 ≤ weights i)
    (hnormal : (∑ i, weights i • a i) = -c)
    (hmargin : (∑ i, weights i * b i) < 1)
    (hinverseWeights : ∀ i, 0 ≤ inverseWeights i)
    (hinverseNormal : (∑ i, inverseWeights i • (a i + b i • c)) = c)
    (hinverseMargin : (∑ i, inverseWeights i * b i) < 1) :
    DiamLE (Hpoly (fun i => a i + b i • c) b) (n - d) := by
  have hdiam := Hirsch.hpoly_diameter_le_excess_of_independent_small_row_blocks dims counts a b T e A hrows hbd hne hcount hsmallcount
  exact HirschProjectiveBlocks.hpoly_diamLE_of_shear_multipliers a b c
    weights inverseWeights hweights hnormal hmargin hinverseWeights
    hinverseNormal hinverseMargin (n-d) hdiam
