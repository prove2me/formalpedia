-- Prove2me | solution 1 for Hirsch.injective_affine_image_diameter_iff
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T14:51:25.742336+00:00
-- url     : https://prove2.me/submissions/d0300dfb-691d-4388-8d4d-878c28b9cddf

import Definitions.Def_Hirsch_model

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

/-- An injective affine map preserves an extreme subset exactly on its image. -/
theorem affineMap_isExtreme_image_iff_of_injective
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) {A B : Set E} :
    IsExtreme ℝ (f '' A) (f '' B) ↔ IsExtreme ℝ A B := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro z hz
      have hfzB : f z ∈ f '' B := ⟨z, hz, rfl⟩
      exact hf.mem_set_image.mp (h.1 hfzB)
    · intro x hx y hy z hz hseg
      have hfx : f x ∈ f '' A := ⟨x, hx, rfl⟩
      have hfy : f y ∈ f '' A := ⟨y, hy, rfl⟩
      have hfz : f z ∈ f '' B := ⟨z, hz, rfl⟩
      have hfseg : f z ∈ openSegment ℝ (f x) (f y) := by
        have hzimg : f z ∈ f '' openSegment ℝ x y := ⟨z, hseg, rfl⟩
        rwa [image_openSegment ℝ f x y] at hzimg
      exact hf.mem_set_image.mp
        (h.left_mem_of_mem_openSegment hfx hfy hfz hfseg)
  · intro h
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, h.1 hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ hzxy
      have hzimg : f z ∈ f '' openSegment ℝ x y := by
        rw [image_openSegment ℝ f x y]
        exact hzxy
      rcases hzimg with ⟨z', hz', hz'eq⟩
      have hzz' : z' = z := hf hz'eq
      subst z'
      exact ⟨x, h.left_mem_of_mem_openSegment hx hy hz hz', rfl⟩

/-- An injective affine map carries exactly the extreme points of a set to the
extreme points of its image. Ambient dimensions may differ. -/
theorem affineMap_image_extremePoints_of_injective
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f) (A : Set E) :
    f '' extremePoints ℝ A = extremePoints ℝ (f '' A) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hs : IsExtreme ℝ A ({x} : Set E) := isExtreme_singleton.mpr hx
    have himg := (affineMap_isExtreme_image_iff_of_injective f hf).2 hs
    have hsingle : IsExtreme ℝ (f '' A) ({f x} : Set F) := by
      simpa using himg
    exact isExtreme_singleton.mp hsingle
  · intro y hy
    rcases hy.1 with ⟨x, hxA, hxy⟩
    subst y
    refine ⟨x, ?_, rfl⟩
    have ht : IsExtreme ℝ (f '' A) ({f x} : Set F) :=
      isExtreme_singleton.mpr hy
    have ht' : IsExtreme ℝ (f '' A) (f '' ({x} : Set E)) := by
      simpa using ht
    exact isExtreme_singleton.mp
      ((affineMap_isExtreme_image_iff_of_injective f hf).1 ht')

/-- Injective affine embeddings preserve and reflect adjacency on the image. -/
theorem affineMap_adj_iff_of_injective
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (A : Set E) (x y : E) :
    Adj (f '' A) (f x) (f y) ↔ Adj A x y := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro hxy
      exact h.1 (congrArg f hxy)
    · have himage : IsExtreme ℝ (f '' A) (f '' segment ℝ x y) := by
        rw [image_segment ℝ f x y]
        exact h.2
      exact (affineMap_isExtreme_image_iff_of_injective f hf).1 himage
  · intro h
    refine ⟨?_, ?_⟩
    · intro hxy
      exact h.1 (hf hxy)
    · have himage :=
        (affineMap_isExtreme_image_iff_of_injective f hf).2 h.2
      rw [image_segment ℝ f x y] at himage
      exact himage

/-- Diameter bounds transport forward through injective affine embeddings. -/
theorem affineMap_diamLE_image_of_injective
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (A : Set E) (B : ℕ) (h : DiamLE A B) :
    DiamLE (f '' A) B := by
  intro u hu v hv
  have huimg : u ∈ f '' extremePoints ℝ A := by
    rw [affineMap_image_extremePoints_of_injective f hf A]
    exact hu
  have hvimg : v ∈ f '' extremePoints ℝ A := by
    rw [affineMap_image_extremePoints_of_injective f hf A]
    exact hv
  rcases huimg with ⟨x, hx, rfl⟩
  rcases hvimg with ⟨y, hy, rfl⟩
  obtain ⟨w, hw0, hwB, hstep⟩ := h x hx y hy
  refine ⟨fun i => f (w i), ?_, ?_, ?_⟩
  · simp only [hw0]
  · simp only [hwB]
  · intro i hi
    rcases hstep i hi with heq | hadj
    · exact Or.inl (congrArg f heq)
    · exact Or.inr ((affineMap_adj_iff_of_injective f hf A _ _).2 hadj)

/-- `DiamLE` is invariant between a set and the image of any injective affine
embedding. This is the dimension-changing transport theorem used by slack maps. -/
theorem affineMap_diamLE_image_iff_of_injective
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (A : Set E) (B : ℕ) :
    DiamLE (f '' A) B ↔ DiamLE A B := by
  classical
  constructor
  · intro h
    intro x hx y hy
    have hfx : f x ∈ extremePoints ℝ (f '' A) := by
      have hmem : f x ∈ f '' extremePoints ℝ A := ⟨x, hx, rfl⟩
      rwa [affineMap_image_extremePoints_of_injective f hf A] at hmem
    have hfy : f y ∈ extremePoints ℝ (f '' A) := by
      have hmem : f y ∈ f '' extremePoints ℝ A := ⟨y, hy, rfl⟩
      rwa [affineMap_image_extremePoints_of_injective f hf A] at hmem
    obtain ⟨w, hw0, hwB, hstep⟩ := h (f x) hfx (f y) hfy
    let g : F → E := Function.invFun f
    refine ⟨fun i => g (w i), ?_, ?_, ?_⟩
    · exact (congrArg g hw0).trans (Function.leftInverse_invFun hf x)
    · exact (congrArg g hwB).trans (Function.leftInverse_invFun hf y)
    · intro i hi
      rcases hstep i hi with heq | hadj
      · exact Or.inl (congrArg g heq)
      · have hwi : w i ∈ f '' A :=
          hadj.2.1 (left_mem_segment ℝ (w i) (w (i + 1)))
        have hwj : w (i + 1) ∈ f '' A :=
          hadj.2.1 (right_mem_segment ℝ (w i) (w (i + 1)))
        rcases hwi with ⟨xi, hxi, hfix⟩
        rcases hwj with ⟨xj, hxj, hfjx⟩
        have hgi : g (w i) = xi := by
          dsimp [g]
          rw [← hfix]
          exact Function.leftInverse_invFun hf xi
        have hgj : g (w (i + 1)) = xj := by
          dsimp [g]
          rw [← hfjx]
          exact Function.leftInverse_invFun hf xj
        have hadj' : Adj (f '' A) (f xi) (f xj) := by
          rw [hfix, hfjx]
          exact hadj
        apply Or.inr
        change Adj A (g (w i)) (g (w (i + 1)))
        rw [hgi, hgj]
        exact (affineMap_adj_iff_of_injective f hf A xi xj).1 hadj'
  · exact affineMap_diamLE_image_of_injective f hf A B

#print axioms affineEquiv_isExtreme_image
#print axioms affineEquiv_image_extremePoints
#print axioms affineEquiv_adj_iff
#print axioms affineEquiv_diamLE_image_iff
#print axioms affineMap_isExtreme_image_iff_of_injective
#print axioms affineMap_image_extremePoints_of_injective
#print axioms affineMap_adj_iff_of_injective
#print axioms affineMap_diamLE_image_iff_of_injective

end Hirsch


theorem solution
    {E F : Type} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    (f : E →ᵃ[ℝ] F) (hf : Function.Injective f)
    (P : Set E) (B : ℕ) :
    Hirsch.DiamLE (f '' P) B ↔ Hirsch.DiamLE P B := by
  exact Hirsch.affineMap_diamLE_image_iff_of_injective f hf P B

#print axioms solution
