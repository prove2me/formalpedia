-- Prove2me | solution 1 for Hirsch.hpoly_diameter_le_excess_of_recursive_projective_products
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T18:49:45.435828+00:00
-- url     : https://prove2.me/submissions/7f2bba60-85ad-42d5-8a1a-eed656add3f5

import Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_rows_le_dim_add_three
import Mathlib
import Definitions.Def_Hirsch_recursive_projective_products
open Set Hirsch
open scoped RealInnerProductSpace

open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschProduct

/-- Concatenate padded walks. This is independent of polytope geometry. -/
lemma append_walk {E : Type*} (R : E → E → Prop)
    {u v z : E} {A B : ℕ}
    (p q : ℕ → E)
    (hp0 : p 0 = u) (hpA : p A = v)
    (hq0 : q 0 = v) (hqB : q B = z)
    (hp : ∀ j < A, p j = p (j + 1) ∨ R (p j) (p (j + 1)))
    (hq : ∀ j < B, q j = q (j + 1) ∨ R (q j) (q (j + 1))) :
    ∃ w : ℕ → E, w 0 = u ∧ w (A + B) = z ∧
      ∀ j < A + B, w j = w (j + 1) ∨ R (w j) (w (j + 1)) := by
  let w : ℕ → E := fun j => if j < A then p j else q (j - A)
  have hleft (j : ℕ) (hj : j ≤ A) : w j = p j := by
    by_cases h : j < A
    · simp only [w, if_pos h]
    · have heq : j = A := by omega
      subst j
      simp only [w, lt_self_iff_false, if_false, Nat.sub_self, hq0, hpA]
  have hright (j : ℕ) (hj : A ≤ j) : w j = q (j - A) := by
    exact if_neg (by omega)
  refine ⟨w, (hleft 0 (Nat.zero_le A)).trans hp0, ?_, ?_⟩
  · rw [hright (A + B) (by omega), Nat.add_sub_cancel_left]
    exact hqB
  · intro j hj
    by_cases hjA : j < A
    · rw [hleft j (by omega), hleft (j + 1) (by omega)]
      exact hp j hjA
    · rw [hright j (by omega), hright (j + 1) (by omega)]
      have hidx : j + 1 - A = (j - A) + 1 := by omega
      rw [hidx]
      exact hq (j - A) (by omega)

lemma pad_walk {E : Type*} (R : E → E → Prop)
    {u v : E} {A B : ℕ} (hAB : A ≤ B)
    (w : ℕ → E) (h0 : w 0 = u) (hA : w A = v)
    (hs : ∀ j < A, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    ∃ w' : ℕ → E, w' 0 = u ∧ w' B = v ∧
      ∀ j < B, w' j = w' (j + 1) ∨ R (w' j) (w' (j + 1)) := by
  let w' : ℕ → E := fun j => w (min j A)
  refine ⟨w', ?_, ?_, ?_⟩
  · simpa only [w', Nat.zero_min] using h0
  · simpa only [w', Nat.min_eq_right hAB] using hA
  · intro j hj
    by_cases hjA : j < A
    · have h0 : j ≤ A := by omega
      have h1 : j + 1 ≤ A := by omega
      simpa only [w', Nat.min_eq_left h0, Nat.min_eq_left h1] using hs j hjA
    · have h0 : A ≤ j := by omega
      have h1 : A ≤ j + 1 := by omega
      exact Or.inl (by simp only [w', Nat.min_eq_right h0, Nat.min_eq_right h1])

variable {ι : Type*} {E : ι → Type*}
variable [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Moving one coordinate along a factor edge, with all other coordinates
fixed at factor vertices, gives a genuine edge of the Cartesian product. -/
lemma update_adj [DecidableEq ι]
    (P : ∀ i, Set (E i)) (base : ∀ i, E i) (i : ι)
    (hfix : ∀ j, j ≠ i → base j ∈ extremePoints ℝ (P j))
    {p q : E i} (hadj : Adj (P i) p q) :
    Adj (Set.univ.pi P) (Function.update base i p) (Function.update base i q) := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    apply hadj.1
    simpa using congrFun heq i
  · intro z hz
    rw [← Pi.image_update_segment] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    rw [Set.mem_univ_pi]
    intro j
    by_cases hji : j = i
    · subst j
      simpa using hadj.2.subset ht
    · simpa [Function.update_of_ne hji] using (hfix j hji).1
  · intro x hx y hy z hz hopen
    rw [Set.mem_univ_pi] at hx hy
    rw [← Pi.image_update_segment] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    obtain ⟨α, β, hα, hβ, hαβ, hcomb⟩ := hopen
    have hop (j : ι) : Function.update base i t j ∈ openSegment ℝ (x j) (y j) :=
      ⟨α, β, hα, hβ, hαβ, congrFun hcomb j⟩
    have hti : t ∈ openSegment ℝ (x i) (y i) := by simpa using hop i
    have hxi : x i ∈ segment ℝ p q :=
      hadj.2.left_mem_of_mem_openSegment (hx i) (hy i) ht hti
    have hxfix (j : ι) (hji : j ≠ i) : x j = base j :=
      (hfix j hji).2 (hx j) (hy j) (by simpa [Function.update_of_ne hji] using hop j)
    rw [← Pi.image_update_segment]
    refine ⟨x i, hxi, ?_⟩
    funext j
    by_cases hji : j = i
    · subst j
      simp
    · simpa [Function.update_of_ne hji] using (hxfix j hji).symm

/-- A finite product has a diameter budget equal to the SUM of factor budgets.
The sum, rather than the total dimension, is the relevant routing quantity. -/
theorem diamLE_pi [Fintype ι]
    (P : ∀ i, Set (E i)) (B : ι → ℕ)
    (hD : ∀ i, DiamLE (P i) (B i)) :
    DiamLE (Set.univ.pi P) (∑ i, B i) := by
  classical
  have hwalk : ∀ s : Finset ι, ∀ u v : ∀ i, E i,
      (∀ i, u i ∈ extremePoints ℝ (P i)) →
      (∀ i, v i ∈ extremePoints ℝ (P i)) →
      (∀ i, i ∉ s → u i = v i) →
      ∃ w : ℕ → (∀ i, E i), w 0 = u ∧ w (∑ i ∈ s, B i) = v ∧
        ∀ j < ∑ i ∈ s, B i,
          w j = w (j + 1) ∨ Adj (Set.univ.pi P) (w j) (w (j + 1)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro u v hu hv heq
        have huv : u = v := funext (fun i => heq i (by simp))
        subst v
        exact ⟨fun _ => u, rfl, rfl, fun _ _ => Or.inl rfl⟩
    | @insert i s his ih =>
        intro u v hu hv heq
        let mid : ∀ j, E j := Function.update u i (v i)
        have hm (j : ι) : mid j ∈ extremePoints ℝ (P j) := by
          by_cases hji : j = i
          · subst j
            simpa [mid] using hv i
          · simpa [mid, Function.update_of_ne hji] using hu j
        have hsame (j : ι) (hjs : j ∉ s) : mid j = v j := by
          by_cases hji : j = i
          · subst j
            simp [mid]
          · simpa [mid, Function.update_of_ne hji] using heq j (by simp [hji, hjs])
        obtain ⟨q, hq0, hqB, hqstep⟩ := ih mid v hm hv hsame
        obtain ⟨p, hp0, hpB, hpstep⟩ := hD i (u i) (hu i) (v i) (hv i)
        let wp : ℕ → (∀ j, E j) := fun t => Function.update u i (p t)
        have hwp0 : wp 0 = u := by simp [wp, hp0]
        have hwpB : wp (B i) = mid := by simp [wp, hpB, mid]
        have hwps : ∀ j < B i, wp j = wp (j + 1) ∨
            Adj (Set.univ.pi P) (wp j) (wp (j + 1)) := by
          intro j hj
          rcases hpstep j hj with h | h
          · exact Or.inl (congrArg (Function.update u i) h)
          · exact Or.inr (update_adj P u i (fun k _ => hu k) h)
        obtain ⟨w, hw0, hwB, hwstep⟩ :=
          append_walk (Adj (Set.univ.pi P)) wp q hwp0 hwpB hq0 hqB hwps hqstep
        refine ⟨w, hw0, ?_, ?_⟩
        · simpa only [Finset.sum_insert his] using hwB
        · simpa only [Finset.sum_insert his] using hwstep
  intro u hu v hv
  have hu' : ∀ i, u i ∈ extremePoints ℝ (P i) := by
    simpa only [extremePoints_pi, Set.mem_univ_pi] using hu
  have hv' : ∀ i, v i ∈ extremePoints ℝ (P i) := by
    simpa only [extremePoints_pi, Set.mem_univ_pi] using hv
  exact hwalk Finset.univ u v hu' hv' (fun i hi => False.elim (hi (Finset.mem_univ i)))


end HirschProduct

end

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

end HirschPerspective

end

/-!
# Affine-equivalence transport for the Hirsch graph predicates

Reusable infrastructure for slack-normalization arguments. Mathlib already
provides affine-map preservation of segments/open segments; this file packages
that into the repository's `extremePoints`, `Adj`, and `DiamLE` predicates.
-/

open Set
open scoped RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Hirsch

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]

private theorem affineEquiv_image_segment
    (f : E ≃ᵃ[ℝ] F) (x y : E) :
    f '' segment ℝ x y = segment ℝ (f x) (f y) := by
  simpa only [AffineEquiv.coe_toAffineMap] using
    (image_segment ℝ f.toAffineMap x y)

private theorem affineEquiv_image_openSegment
    (f : E ≃ᵃ[ℝ] F) (x y : E) :
    f '' openSegment ℝ x y = openSegment ℝ (f x) (f y) := by
  simpa only [AffineEquiv.coe_toAffineMap] using
    (image_openSegment ℝ f.toAffineMap x y)

/-- Affine equivalences preserve extreme subsets under image. -/
theorem affineEquiv_isExtreme_image
    (f : E ≃ᵃ[ℝ] F) {A B : Set E} (h : IsExtreme ℝ A B) :
    IsExtreme ℝ (f '' A) (f '' B) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, h.1 hx, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hzxy
    have hzimg : f z ∈ f '' openSegment ℝ x y := by
      rw [affineEquiv_image_openSegment f x y]
      exact hzxy
    rcases hzimg with ⟨z', hz', hz'eq⟩
    have hzz' : z' = z := f.injective hz'eq
    subst z'
    exact ⟨x, h.left_mem_of_mem_openSegment hx hy hz hz', rfl⟩

/-- Affine equivalences preserve and reflect extreme subsets. -/
theorem affineEquiv_isExtreme_image_iff
    (f : E ≃ᵃ[ℝ] F) {A B : Set E} :
    IsExtreme ℝ (f '' A) (f '' B) ↔ IsExtreme ℝ A B := by
  constructor
  · intro h
    have h' := affineEquiv_isExtreme_image f.symm h
    have hbackA : f.symm '' (f '' A) = A := by
      ext x
      simp
    have hbackB : f.symm '' (f '' B) = B := by
      ext x
      simp
    rw [hbackA, hbackB] at h'
    exact h'
  · exact affineEquiv_isExtreme_image f

/-- Affine equivalences carry exactly the extreme points to the extreme points
of the image set. -/
theorem affineEquiv_image_extremePoints
    (f : E ≃ᵃ[ℝ] F) (A : Set E) :
    f '' extremePoints ℝ A = extremePoints ℝ (f '' A) := by
  ext b
  obtain ⟨a, rfl⟩ := f.surjective b
  have himage : ∀ x y, f '' openSegment ℝ x y = openSegment ℝ (f x) (f y) :=
    affineEquiv_image_openSegment f
  simp only [mem_extremePoints, f.surjective.forall,
    f.injective.mem_set_image, f.injective.eq_iff, ← himage]

/-- An affine equivalence preserves and reflects graph adjacency. -/
theorem affineEquiv_adj_iff
    (f : E ≃ᵃ[ℝ] F) (A : Set E) (x y : E) :
    Adj (f '' A) (f x) (f y) ↔ Adj A x y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hxy
      exact h.1 (congrArg f hxy)
    · have himage : IsExtreme ℝ (f '' A) (f '' segment ℝ x y) := by
        rw [affineEquiv_image_segment f x y]
        exact h.2
      exact (affineEquiv_isExtreme_image_iff f).mp himage
  · intro h
    refine ⟨?_, ?_⟩
    · intro hxy
      exact h.1 (f.injective hxy)
    · have himage := affineEquiv_isExtreme_image f h.2
      rw [affineEquiv_image_segment f x y] at himage
      exact himage

/-- A graph-diameter bound transports forward through an affine equivalence. -/
theorem affineEquiv_diamLE_image
    (f : E ≃ᵃ[ℝ] F) (A : Set E) (B : ℕ)
    (h : DiamLE A B) : DiamLE (f '' A) B := by
  intro u hu v hv
  obtain ⟨x, rfl⟩ := f.surjective u
  obtain ⟨y, rfl⟩ := f.surjective v
  have hximg : f x ∈ f '' extremePoints ℝ A := by
    rw [affineEquiv_image_extremePoints f A]
    exact hu
  have hyimg : f y ∈ f '' extremePoints ℝ A := by
    rw [affineEquiv_image_extremePoints f A]
    exact hv
  have hx : x ∈ extremePoints ℝ A := f.injective.mem_set_image.mp hximg
  have hy : y ∈ extremePoints ℝ A := f.injective.mem_set_image.mp hyimg
  obtain ⟨w, hw0, hwB, hstep⟩ := h x hx y hy
  refine ⟨fun i => f (w i), ?_, ?_, ?_⟩
  · simp only [hw0]
  · simp only [hwB]
  · intro i hi
    rcases hstep i hi with heq | hadj
    · exact Or.inl (congrArg f heq)
    · exact Or.inr ((affineEquiv_adj_iff f A (w i) (w (i + 1))).2 hadj)

/-- `DiamLE` is invariant under affine equivalence. -/
theorem affineEquiv_diamLE_image_iff
    (f : E ≃ᵃ[ℝ] F) (A : Set E) (B : ℕ) :
    DiamLE (f '' A) B ↔ DiamLE A B := by
  constructor
  · intro h
    have h' := affineEquiv_diamLE_image f.symm (f '' A) B h
    have hback : f.symm '' (f '' A) = A := by
      ext x
      simp
    rw [hback] at h'
    exact h'
  · exact affineEquiv_diamLE_image f A B


end Hirsch

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschRowBlocks

/-- An algebraic row-block certificate identifies the entire feasible set with
an actual Cartesian product. Unlike a face-cover certificate, every combination
of factor points is feasible; there is no missing portal or compatibility premise. -/
theorem image_hpoly_eq_pi_of_row_blocks
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫) :
    T '' Hpoly a b = Set.univ.pi
      (fun i => Hpoly (A i) (fun j => b (e ⟨i, j⟩))) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Set.mem_univ_pi]
    intro i j
    have hr := hrows (T x) i j
    rw [T.symm_apply_apply] at hr
    rw [← hr]
    exact hx (e ⟨i, j⟩)
  · intro hz
    rw [Set.mem_univ_pi] at hz
    refine ⟨T.symm z, ?_, T.apply_symm_apply z⟩
    intro r
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective r
    rw [hrows]
    exact hz i j

/-- Factor boundedness is inherited from a nonempty bounded parent; it is not
an additional geometric assumption supplied by the certificate. -/
theorem factors_bounded_of_row_blocks
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty) :
    ∀ i, Bornology.IsBounded (Hpoly (A i) (fun j => b (e ⟨i, j⟩))) := by
  have himage := image_hpoly_eq_pi_of_row_blocks dims counts a b T e A hrows
  have hb : Bornology.IsBounded (T '' Hpoly a b) :=
    T.toContinuousLinearEquiv.toContinuousLinearMap.lipschitz.isBounded_image hbd
  have hn : (T '' Hpoly a b).Nonempty := hne.image T
  rw [himage] at hb hn
  exact (Bornology.isBounded_pi_of_nonempty hn).mp hb

/-- The row and coordinate equivalences force additive presentation excess.
The lower row-count checks make natural subtraction honest. -/
theorem row_block_excess_sum
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (hcount : ∀ i, dims i ≤ counts i) :
    (∑ i, (counts i - dims i)) = n - d := by
  have hd : d = ∑ i, dims i := by
    simpa [Module.finrank_pi_fintype] using T.finrank_eq
  have hn : (∑ i, counts i) = n := by
    simpa using Fintype.card_congr e
  have hsplit : (∑ i, counts i) = (∑ i, dims i) +
      ∑ i, (counts i - dims i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (Nat.add_sub_of_le (hcount i)).symm
  omega


end HirschRowBlocks
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


end HirschProjectiveBlocks
end

/-!
# Recursive projective product certificates with telescoping edge budgets

Each node may use its OWN positive projective chart. This is strictly more
flexible than one chart exposing all small-excess factors. Node hypotheses are
actual row identities, affine equivalences and denominator signs; leaves use
only boundedness and the known small-excess row-count condition.

The small-excess theorem is explicit. No conjectural diameter child is added.
The geometric predicate has a standalone public definition interface. Local
compilation and publication receipts are maintained separately from the proof.
-/
open Set Hirsch HirschPerspective HirschProjectiveBlocks
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace HirschRecursiveProducts

/-- Sum all leaf excesses exactly once. Products ADD costs and projective/affine
transport preserves them, so no cost multiplier appears at an internal node. -/
theorem ProductTree.diamLE
    (hsmall : ∀ {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
      (b : Fin n → ℝ), Bornology.IsBounded (Hpoly a b) →
      n ≤ d + 3 → DiamLE (Hpoly a b) (n-d))
    {d n : ℕ} {a : Fin n → EuclideanSpace ℝ (Fin d)} {b : Fin n → ℝ}
    (cert : ProductTree a b) : DiamLE (Hpoly a b) (n-d) := by
  induction cert with
  | leaf hbd hcount => exact hsmall _ _ hbd hcount
  | affine f himage prior ih =>
      have h := Hirsch.affineEquiv_diamLE_image f _ _ ih
      rwa [himage] at h
  | split dims counts a b T e A hrows hcount hk hdim c hsource htarget children ih =>
      have hprod := HirschProduct.diamLE_pi
        (fun i => Hpoly (A i) (fun j => b (e ⟨i,j⟩)))
        (fun i => counts i - dims i) ih
      rw [HirschRowBlocks.row_block_excess_sum dims counts T e hcount] at hprod
      rw [← HirschRowBlocks.image_hpoly_eq_pi_of_row_blocks
        dims counts a b T e A hrows] at hprod
      have hbase := (Hirsch.affineEquiv_diamLE_image_iff
        T.toAffineEquiv (Hpoly a b) _).mp hprod
      exact hpoly_diamLE_of_positive_shear a b c _ hsource htarget hbase


end HirschRecursiveProducts
end

theorem solution {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (cert : HirschRecursiveProducts.ProductTree a b) : DiamLE (Hpoly a b) (n-d) := by
  apply HirschRecursiveProducts.ProductTree.diamLE ?_ cert
  intro d n a b hbd hrows
  exact Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three d n a b hrows hbd
