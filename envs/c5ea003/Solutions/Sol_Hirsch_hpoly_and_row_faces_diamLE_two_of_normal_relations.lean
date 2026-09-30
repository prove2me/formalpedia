-- Prove2me | solution 1 for Hirsch.hpoly_and_row_faces_diamLE_two_of_normal_relations
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T15:56:47.889315+00:00
-- url     : https://prove2.me/submissions/5e888ccf-0f16-48a1-8992-50d3debf1258

import Definitions.Def_Hirsch_model
import Mathlib

/- Frozen source: Solutions/PolynomialAffineDiameterTransport.lean -/
section

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

end

/- Frozen source: Solutions/PolynomialExcessTwoMomentSlice.lean -/
section

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwo

/-- Normalized slack model for an H-polytope with row excess two:
nonnegative coordinates with total mass one and one affine moment. -/
def momentSlice {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {s | (∀ i, 0 ≤ s i) ∧ (∑ i, s i) = 1 ∧ (∑ i, t i * s i) = mu}

/-- The coordinate-zero support face of a normalized moment slice. -/
def zeroFace {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {s | s ∈ momentSlice t mu ∧ s i = 0}

lemma zeroFace_subset {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) :
    zeroFace t mu i ⊆ momentSlice t mu := by
  intro s hs
  exact hs.1

/-- Nonnegativity makes every coordinate-zero support condition an extreme
face. This is the basic face-preservation fact used by the excess-two portal
selector. -/
theorem zeroFace_isExtreme {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) :
    IsExtreme ℝ (momentSlice t mu) (zeroFace t mu i) := by
  refine ⟨zeroFace_subset t mu i, ?_⟩
  intro x hx y hy z hz hzseg
  rcases (mem_openSegment_iff_div.mp hzseg) with ⟨a, b, ha, hb, hcomb⟩
  have hab : 0 < a + b := add_pos ha hb
  have hapos : 0 < a / (a + b) := div_pos ha hab
  have hbpos : 0 < b / (a + b) := div_pos hb hab
  have hxnon : 0 ≤ x i := hx.1 i
  have hynon : 0 ≤ y i := hy.1 i
  have hz0 : z i = 0 := hz.2
  have hcoord : (a / (a + b)) * x i + (b / (a + b)) * y i = z i := by
    have h := congrArg (fun q : EuclideanSpace ℝ (Fin n) => q i) hcomb
    simpa [smul_eq_mul] using h
  have hxi : x i = 0 := by
    rw [hz0] at hcoord
    nlinarith
  exact ⟨hx, hxi⟩

/-- A finite sum supported only on two distinct indices reduces to those two
terms. This is used repeatedly by the explicit moment-slice coordinates. -/
lemma sum_eq_add_of_zero_off_pair {n : ℕ}
    (f : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j)
    (hzero : ∀ k, k ≠ i → k ≠ j → f k = 0) :
    (∑ k, f k) = f i + f j := by
  classical
  have hsub : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := by simp
  have hsmall :
      (∑ k ∈ ({i, j} : Finset (Fin n)), f k) =
        ∑ k ∈ (Finset.univ : Finset (Fin n)), f k := by
    apply Finset.sum_subset hsub
    intro k _ hk
    apply hzero k
    · intro hki
      subst k
      exact hk (by simp)
    · intro hkj
      subst k
      exact hk (by simp)
  calc
    (∑ k, f k) = ∑ k ∈ (Finset.univ : Finset (Fin n)), f k := rfl
    _ = ∑ k ∈ ({i, j} : Finset (Fin n)), f k := hsmall.symm
    _ = f i + f j := by simp [hij]

/-- The unique feasible point supported on a low index `i` and a high index
`j`. The hypotheses ensuring `t i < mu < t j` are supplied to the lemmas. -/
def pairPoint {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k =>
    if k = i then (t j - mu) / (t j - t i)
    else if k = j then (mu - t i) / (t j - t i)
    else 0)

@[simp] lemma pairPoint_apply_left {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n) :
    pairPoint t mu i j i = (t j - mu) / (t j - t i) := by
  simp [pairPoint]

@[simp] lemma pairPoint_apply_right {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n) (hij : i ≠ j) :
    pairPoint t mu i j j = (mu - t i) / (t j - t i) := by
  simp [pairPoint, hij.symm]

@[simp] lemma pairPoint_apply_other {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hki : k ≠ i) (hkj : k ≠ j) :
    pairPoint t mu i j k = 0 := by
  simp [pairPoint, hki, hkj]

/-- The explicit two-supported point satisfies the two moment equations. -/
theorem pairPoint_mem {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hli : t i < mu) (hrj : mu < t j) :
    pairPoint t mu i j ∈ momentSlice t mu := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  have hden : 0 < t j - t i := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro k
    by_cases hki : k = i
    · subst k
      rw [pairPoint_apply_left]
      positivity
    · by_cases hkj : k = j
      · subst k
        rw [pairPoint_apply_right t mu i j hij]
        positivity
      · rw [pairPoint_apply_other t mu i j k hki hkj]
  · have hsum := sum_eq_add_of_zero_off_pair
      (fun k => pairPoint t mu i j k) i j hij
      (fun k hki hkj => pairPoint_apply_other t mu i j k hki hkj)
    rw [hsum]
    change pairPoint t mu i j i + pairPoint t mu i j j = 1
    rw [pairPoint_apply_left, pairPoint_apply_right t mu i j hij]
    field_simp [ne_of_gt hden]
    ring
  · have hsum := sum_eq_add_of_zero_off_pair
      (fun k => t k * pairPoint t mu i j k) i j hij (by
        intro k hki hkj
        change t k * pairPoint t mu i j k = 0
        rw [pairPoint_apply_other t mu i j k hki hkj, mul_zero])
    rw [hsum]
    change t i * pairPoint t mu i j i + t j * pairPoint t mu i j j = mu
    rw [pairPoint_apply_left, pairPoint_apply_right t mu i j hij]
    field_simp [ne_of_gt hden]
    ring

#print axioms zeroFace_isExtreme
#print axioms sum_eq_add_of_zero_off_pair
#print axioms pairPoint_mem

end HirschExcessTwo

end

end

/- Frozen source: Solutions/PolynomialExcessTwoPairVertices.lean -/
section

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwo

/-- A feasible point of the normalized moment slice whose support is contained
in a low/high pair is the explicit `pairPoint` on that pair. -/
theorem eq_pairPoint_of_mem_of_zero_off_pair {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hli : t i < mu) (hrj : mu < t j)
    (s : EuclideanSpace ℝ (Fin n)) (hs : s ∈ momentSlice t mu)
    (hzero : ∀ k, k ≠ i → k ≠ j → s k = 0) :
    s = pairPoint t mu i j := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  have hden : 0 < t j - t i := by linarith
  have hmassSum := sum_eq_add_of_zero_off_pair (fun k => s k) i j hij hzero
  have hmass : s i + s j = 1 := by
    calc
      s i + s j = ∑ k, s k := hmassSum.symm
      _ = 1 := hs.2.1
  have hmomSum := sum_eq_add_of_zero_off_pair
    (fun k => t k * s k) i j hij (by
      intro k hki hkj
      change t k * s k = 0
      rw [hzero k hki hkj, mul_zero])
  have hmom : t i * s i + t j * s j = mu := by
    calc
      t i * s i + t j * s j = ∑ k, t k * s k := hmomSum.symm
      _ = mu := hs.2.2
  have hsi_mul : s i * (t j - t i) = t j - mu := by
    linear_combination t j * hmass - hmom
  have hsj_mul : s j * (t j - t i) = mu - t i := by
    linear_combination hmom - t i * hmass
  have hsi : s i = (t j - mu) / (t j - t i) :=
    (eq_div_iff (ne_of_gt hden)).2 hsi_mul
  have hsj : s j = (mu - t i) / (t j - t i) :=
    (eq_div_iff (ne_of_gt hden)).2 hsj_mul
  ext k
  by_cases hki : k = i
  · subst k
    change s i = pairPoint t mu i j i
    rw [hsi, pairPoint_apply_left]
  · by_cases hkj : k = j
    · subst k
      change s j = pairPoint t mu i j j
      rw [hsj, pairPoint_apply_right t mu i j hij]
    · change s k = pairPoint t mu i j k
      rw [hzero k hki hkj, pairPoint_apply_other t mu i j k hki hkj]

/-- Every low/high two-support point is an actual extreme vertex of the
normalized moment slice. The proof uses only coordinate-zero extreme faces
and the two moment equations; no global vertex enumeration is used. -/
theorem pairPoint_mem_extremePoints {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hli : t i < mu) (hrj : mu < t j) :
    pairPoint t mu i j ∈ extremePoints ℝ (momentSlice t mu) := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  have hp : pairPoint t mu i j ∈ momentSlice t mu := pairPoint_mem t mu i j hli hrj
  rw [mem_extremePoints_iff_left]
  refine ⟨hp, ?_⟩
  intro x hx y hy hseg
  apply eq_pairPoint_of_mem_of_zero_off_pair t mu i j hli hrj x hx
  intro k hki hkj
  have hpzero : pairPoint t mu i j ∈ zeroFace t mu k := by
    exact ⟨hp, pairPoint_apply_other t mu i j k hki hkj⟩
  have hxzero := (zeroFace_isExtreme t mu k).left_mem_of_mem_openSegment hx hy hpzero hseg
  exact hxzero.2

#print axioms eq_pairPoint_of_mem_of_zero_off_pair
#print axioms pairPoint_mem_extremePoints

end HirschExcessTwo

end

end

/- Frozen source: Solutions/PolynomialExcessTwoSupportFaces.lean -/
section

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwo

/-- The face obtained by requiring all coordinates outside `S` to vanish. -/
def supportFace {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {s | s ∈ momentSlice t mu ∧ ∀ k, k ∉ S → s k = 0}

lemma supportFace_subset {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n)) :
    supportFace t mu S ⊆ momentSlice t mu := by
  intro s hs
  exact hs.1

/-- Coordinate support carriers are extreme faces. This packages simultaneous
preservation of all common zero coordinates into one face. -/
theorem supportFace_isExtreme {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n)) :
    IsExtreme ℝ (momentSlice t mu) (supportFace t mu S) := by
  refine ⟨supportFace_subset t mu S, ?_⟩
  intro x hx y hy z hz hseg
  refine ⟨hx, ?_⟩
  intro k hk
  have hz0 : z ∈ zeroFace t mu k := ⟨hz.1, hz.2 k hk⟩
  have hx0 := (zeroFace_isExtreme t mu k).left_mem_of_mem_openSegment hx hy hz0 hseg
  exact hx0.2

/-- A low/high pair vertex belongs to every support carrier containing its two
indices. -/
lemma pairPoint_mem_supportFace {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hli : t i < mu) (hrj : mu < t j)
    (S : Finset (Fin n)) (hiS : i ∈ S) (hjS : j ∈ S) :
    pairPoint t mu i j ∈ supportFace t mu S := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  refine ⟨pairPoint_mem t mu i j hli hrj, ?_⟩
  intro k hk
  have hki : k ≠ i := by
    intro h
    subst k
    exact hk hiS
  have hkj : k ≠ j := by
    intro h
    subst k
    exact hk hjS
  exact pairPoint_apply_other t mu i j k hki hkj

#print axioms supportFace_isExtreme
#print axioms pairPoint_mem_supportFace

end HirschExcessTwo

end

end

/- Frozen source: Solutions/PolynomialExcessTwoConvexity.lean -/
section

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwo

/-- The normalized moment slice is convex. -/
theorem momentSlice_convex {n : ℕ} (t : Fin n → ℝ) (mu : ℝ) :
    Convex ℝ (momentSlice t mu) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change 0 ≤ a * x i + b * y i
    nlinarith [hx.1 i, hy.1 i]
  · change (∑ i, (a * x i + b * y i)) = 1
    calc
      (∑ i, (a * x i + b * y i)) =
          a * (∑ i, x i) + b * (∑ i, y i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = a * 1 + b * 1 := by rw [hx.2.1, hy.2.1]
      _ = 1 := by nlinarith
  · change (∑ i, t i * (a * x i + b * y i)) = mu
    calc
      (∑ i, t i * (a * x i + b * y i)) =
          ∑ i, (a * (t i * x i) + b * (t i * y i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = a * (∑ i, t i * x i) + b * (∑ i, t i * y i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ = a * mu + b * mu := by rw [hx.2.2, hy.2.2]
      _ = (a + b) * mu := by ring
      _ = mu := by rw [hab, one_mul]

/-- The segment between two points of one support carrier remains in that
support carrier. -/
theorem segment_subset_supportFace {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n))
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ supportFace t mu S) (hy : y ∈ supportFace t mu S) :
    segment ℝ x y ⊆ supportFace t mu S := by
  intro z hz
  have hzP : z ∈ momentSlice t mu :=
    (momentSlice_convex t mu).segment_subset hx.1 hy.1 hz
  refine ⟨hzP, ?_⟩
  intro k hk
  rcases mem_segment_iff_div.mp hz with ⟨a, b, ha, hb, hab, hcomb⟩
  have hcoord := congrArg (fun q : EuclideanSpace ℝ (Fin n) => q k) hcomb
  have hx0 := hx.2 k hk
  have hy0 := hy.2 k hk
  simpa [hx0, hy0] using hcoord.symm

#print axioms momentSlice_convex
#print axioms segment_subset_supportFace

end HirschExcessTwo

end

end

/- Frozen source: Solutions/PolynomialExcessTwoVertexClassification.lean -/
section

/-!
# All vertices of the normalized two-moment slice

Candidate continuation of main after PR85. This file has NOT been compiled.
No Lean-kernel or Prove2Me verification is claimed. See the accompanying
research note and exact-rational tests for the ordinary proof and evidence.

The support-domination argument avoids assuming generic moments, dimension,
nonemptiness, strict feasibility, or a pre-existing enumeration of vertices.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschExcessTwo

/-- Unit mass at one coordinate. This is feasible exactly when its moment
is the prescribed moment. -/
def singletonPoint {n : ℕ} (i : Fin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun k => if k = i then 1 else 0)

@[simp] lemma singletonPoint_apply {n : ℕ} (i k : Fin n) :
    singletonPoint i k = if k = i then 1 else 0 := rfl

lemma singletonPoint_mem {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) (hi : t i = mu) :
    singletonPoint i ∈ momentSlice t mu := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro k
    simp only [singletonPoint_apply]
    split_ifs <;> norm_num
  · change (∑ k : Fin n, if k = i then (1 : ℝ) else 0) = 1
    simp
  · change (∑ k : Fin n, t k * (if k = i then (1 : ℝ) else 0)) = mu
    simp [mul_ite, hi]

lemma eq_singletonPoint_of_zero_off {n : ℕ}
    (s : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hmass : (∑ k, s k) = 1)
    (hzero : ∀ k, k ≠ i → s k = 0) : s = singletonPoint i := by
  classical
  have hsum : (∑ k, s k) = s i := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      exact hzero k hki
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have hsi : s i = 1 := hsum.symm.trans hmass
  ext k
  change s k = singletonPoint i k
  by_cases hki : k = i
  · subst k
    simpa using hsi
  · simp [singletonPoint_apply, hki, hzero k hki]

/-- Equal-moment singletons are extreme, including repeated equal moments. -/
theorem singletonPoint_mem_extremePoints {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) (hi : t i = mu) :
    singletonPoint i ∈ extremePoints ℝ (momentSlice t mu) := by
  classical
  have hp := singletonPoint_mem t mu i hi
  rw [mem_extremePoints_iff_left]
  refine ⟨hp, ?_⟩
  intro x hx y hy hseg
  apply eq_singletonPoint_of_zero_off x i hx.2.1
  intro k hki
  have hpzero : singletonPoint i ∈ zeroFace t mu k := by
    refine ⟨hp, ?_⟩
    simp [singletonPoint_apply, hki]
  exact ((zeroFace_isExtreme t mu k).left_mem_of_mem_openSegment
    hx hy hpzero hseg).2

/-- A finite positive margin absorbs a sufficiently small common perturbation.
The proof is elementary finite induction; no optimization oracle is used. -/
private theorem exists_positive_small_scale
    {ι : Type*} (S : Finset ι) (c r : ι → ℝ) :
    (∀ i ∈ S, 0 < r i) →
      ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε * |c i| < r i := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨1, by norm_num, ?_⟩
      simp
  | @insert i S hi ih =>
      intro hr
      obtain ⟨ε, hε, hS⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
      have hri : 0 < r i := hr i (Finset.mem_insert_self i S)
      have hden : 0 < |c i| + 1 := by positivity
      let δ : ℝ := min ε (r i / (|c i| + 1))
      have hδ : 0 < δ := lt_min hε (div_pos hri hden)
      have hδε : δ ≤ ε := min_le_left _ _
      have hδr : δ * (|c i| + 1) ≤ r i :=
        (le_div_iff₀ hden).mp (min_le_right _ _)
      refine ⟨δ / 2, by positivity, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        nlinarith [abs_nonneg (c i)]
      · calc
          (δ / 2) * |c j| ≤ ε * |c j| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg (c j))
          _ < r j := hS j hjS

/-- An extreme point equals every feasible point supported inside its positive
coordinates. This supplies classification without a support-rank assumption. -/
theorem extreme_eq_of_support_contained {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ extremePoints ℝ (momentSlice t mu))
    (hy : y ∈ momentSlice t mu)
    (hsupp : ∀ k, x k = 0 → y k = 0) : x = y := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun k => 0 < x k)
  obtain ⟨ε, hε, hsmall⟩ := exists_positive_small_scale S
    (fun k => y k) (fun k => x k)
    (by intro k hk; exact (Finset.mem_filter.mp hk).2)
  let θ : ℝ := min ε (1 / 2)
  have hθ : 0 < θ := lt_min hε (by norm_num)
  have hθε : θ ≤ ε := min_le_left _ _
  have hθhalf : θ ≤ 1 / 2 := min_le_right _ _
  have hθ1 : θ < 1 := by linarith
  have hden : 0 < 1 - θ := sub_pos.mpr hθ1
  have hdom : ∀ k, θ * y k ≤ x k := by
    intro k
    by_cases hk : 0 < x k
    · have hkS : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
      have hbound := hsmall k hkS
      rw [abs_of_nonneg (hy.1 k)] at hbound
      exact (mul_le_mul_of_nonneg_right hθε (hy.1 k)).trans hbound.le
    · have hx0 : x k = 0 := le_antisymm (le_of_not_gt hk) (hx.1.1 k)
      rw [hx0, hsupp k hx0, mul_zero]
  let z : EuclideanSpace ℝ (Fin n) :=
    WithLp.toLp 2 (fun k => (x k - θ * y k) / (1 - θ))
  have hzcoord (k : Fin n) : z k = (x k - θ * y k) / (1 - θ) := rfl
  have hz : z ∈ momentSlice t mu := by
    refine ⟨?_, ?_, ?_⟩
    · intro k
      rw [hzcoord]
      exact div_nonneg (sub_nonneg.mpr (hdom k)) hden.le
    · change (∑ k, (x k - θ * y k) / (1 - θ)) = 1
      rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hx.1.2.1, hy.2.1, mul_one]
      exact div_self (ne_of_gt hden)
    · change (∑ k, t k * ((x k - θ * y k) / (1 - θ))) = mu
      calc
        (∑ k, t k * ((x k - θ * y k) / (1 - θ))) =
            (∑ k, (t k * x k - θ * (t k * y k))) / (1 - θ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = (mu - θ * mu) / (1 - θ) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hx.1.2.2, hy.2.2]
        _ = mu := by field_simp [ne_of_gt hden]
  have hcomb : θ • y + (1 - θ) • z = x := by
    ext k
    change θ * y k + (1 - θ) * z k = x k
    rw [hzcoord]
    field_simp [ne_of_gt hden]
    ring
  have hseg : x ∈ openSegment ℝ y z := by
    apply mem_openSegment_iff_div.mpr
    refine ⟨θ, 1 - θ, hθ, hden, ?_⟩
    have hsum : θ + (1 - θ) = 1 := by ring
    simpa only [hsum, div_one] using hcomb
  exact (hx.2 hy hz hseg).symm

/-- A feasible distribution either has a positive equal-moment coordinate,
or has positive coordinates strictly on both sides of the target moment. -/
theorem feasible_support_has_singleton_or_pair {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ momentSlice t mu) :
    (∃ k : Fin n, 0 < x k ∧ t k = mu) ∨
      ∃ i j : Fin n, 0 < x i ∧ 0 < x j ∧ t i < mu ∧ mu < t j := by
  classical
  by_cases he : ∃ k : Fin n, 0 < x k ∧ t k = mu
  · exact Or.inl he
  right
  have hne (k : Fin n) (hk : 0 < x k) : t k ≠ mu := by
    intro h
    exact he ⟨k, hk, h⟩
  have hpos : ∃ k : Fin n, 0 < x k := by
    by_contra h
    have hz : ∀ k, x k = 0 := by
      intro k
      exact le_antisymm (le_of_not_gt (fun hk => h ⟨k, hk⟩)) (hx.1 k)
    have hsum : (∑ k, x k) = 0 := by simp [hz]
    linarith [hx.2.1]
  obtain ⟨r, hr⟩ := hpos
  have hsum : (∑ k, (t k - mu) * x k) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hx.2.2, hx.2.1]
    ring
  have hsum' : (∑ k, (mu - t k) * x k) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hx.2.2, hx.2.1]
    ring
  have hl : ∃ i : Fin n, 0 < x i ∧ t i < mu := by
    by_contra h
    have hge (k : Fin n) (hk : 0 < x k) : mu ≤ t k :=
      le_of_not_gt (fun ht => h ⟨k, hk, ht⟩)
    have hnn : ∀ k : Fin n, 0 ≤ (t k - mu) * x k := by
      intro k
      by_cases hk : 0 < x k
      · exact mul_nonneg (sub_nonneg.mpr (hge k hk)) (hx.1 k)
      · have hz : x k = 0 := le_antisymm (le_of_not_gt hk) (hx.1 k)
        simp [hz]
    have htr : mu < t r := lt_of_le_of_ne (hge r hr) (hne r hr).symm
    have hp : 0 < (t r - mu) * x r := mul_pos (sub_pos.mpr htr) hr
    have hb := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hnn k)
      (Finset.mem_univ r)
    rw [hsum] at hb
    linarith
  have hh : ∃ j : Fin n, 0 < x j ∧ mu < t j := by
    by_contra h
    have hle (k : Fin n) (hk : 0 < x k) : t k ≤ mu :=
      le_of_not_gt (fun ht => h ⟨k, hk, ht⟩)
    have hnn : ∀ k : Fin n, 0 ≤ (mu - t k) * x k := by
      intro k
      by_cases hk : 0 < x k
      · exact mul_nonneg (sub_nonneg.mpr (hle k hk)) (hx.1 k)
      · have hz : x k = 0 := le_antisymm (le_of_not_gt hk) (hx.1 k)
        simp [hz]
    have htr : t r < mu := lt_of_le_of_ne (hle r hr) (hne r hr)
    have hp : 0 < (mu - t r) * x r := mul_pos (sub_pos.mpr htr) hr
    have hb := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hnn k)
      (Finset.mem_univ r)
    rw [hsum'] at hb
    linarith
  obtain ⟨i, hi, hti⟩ := hl
  obtain ⟨j, hj, htj⟩ := hh
  exact ⟨i, j, hi, hj, hti, htj⟩

/-- Complete classification, not just existence of the listed vertices. -/
theorem momentSlice_extremePoints_iff {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ extremePoints ℝ (momentSlice t mu) ↔
      (∃ k : Fin n, t k = mu ∧ x = singletonPoint k) ∨
      (∃ i j : Fin n, t i < mu ∧ mu < t j ∧ x = pairPoint t mu i j) := by
  classical
  constructor
  · intro hx
    rcases feasible_support_has_singleton_or_pair t mu x hx.1 with
      ⟨k, hk, htk⟩ | ⟨i, j, hi, hj, hti, htj⟩
    · left
      refine ⟨k, htk, ?_⟩
      apply extreme_eq_of_support_contained t mu x (singletonPoint k) hx
        (singletonPoint_mem t mu k htk)
      intro r hr
      have hrk : r ≠ k := by intro h; subst r; linarith
      simp [singletonPoint_apply, hrk]
    · right
      refine ⟨i, j, hti, htj, ?_⟩
      apply extreme_eq_of_support_contained t mu x (pairPoint t mu i j) hx
        (pairPoint_mem t mu i j hti htj)
      intro r hr
      have hri : r ≠ i := by intro h; subst r; linarith
      have hrj : r ≠ j := by intro h; subst r; linarith
      exact pairPoint_apply_other t mu i j r hri hrj
  · rintro (⟨k, hk, rfl⟩ | ⟨i, j, hi, hj, rfl⟩)
    · exact singletonPoint_mem_extremePoints t mu k hk
    · exact pairPoint_mem_extremePoints t mu i j hi hj

#print axioms singletonPoint_mem_extremePoints
#print axioms extreme_eq_of_support_contained
#print axioms feasible_support_has_singleton_or_pair
#print axioms momentSlice_extremePoints_iff

end HirschExcessTwo

end

end

/- Frozen source: Solutions/PolynomialExcessTwoSharedAdjacency.lean -/
section

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000
set_option autoImplicit false

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschExcessTwo

/-- A finite sum supported on three distinct indices reduces to those three
terms. -/
lemma sum_eq_add_add_of_zero_off_triple {n : ℕ}
    (f : Fin n → ℝ) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → f r = 0) :
    (∑ r, f r) = f i + f j + f k := by
  classical
  have hsub : ({i, j, k} : Finset (Fin n)) ⊆ Finset.univ := by simp
  have hsmall :
      (∑ r ∈ ({i, j, k} : Finset (Fin n)), f r) =
        ∑ r ∈ (Finset.univ : Finset (Fin n)), f r := by
    apply Finset.sum_subset hsub
    intro r _ hr
    apply hzero r
    · intro hri
      subst r
      exact hr (by simp)
    · intro hrj
      subst r
      exact hr (by simp)
    · intro hrk
      subst r
      exact hr (by simp)
  calc
    (∑ r, f r) = ∑ r ∈ (Finset.univ : Finset (Fin n)), f r := rfl
    _ = ∑ r ∈ ({i, j, k} : Finset (Fin n)), f r := hsmall.symm
    _ = f i + f j + f k := by
      simp [hij, hik, hjk, add_comm, add_left_comm]

/-- With one low index and two distinct high indices, the corresponding
three-coordinate support face is exactly the segment joining the two pair
vertices. -/
theorem supportFace_triple_eq_segment_shared_low {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hli : t i < mu) (hrj : mu < t j) (hrk : mu < t k)
    (hjk : j ≠ k) :
    supportFace t mu {i, j, k} =
      segment ℝ (pairPoint t mu i j) (pairPoint t mu i k) := by
  classical
  have hij : i ≠ j := by
    intro h
    subst j
    linarith
  have hik : i ≠ k := by
    intro h
    subst k
    linarith
  have hji : j ≠ i := hij.symm
  have hki : k ≠ i := hik.symm
  have hkj : k ≠ j := hjk.symm
  have hdj : 0 < t j - t i := by linarith
  have hdk : 0 < t k - t i := by linarith
  have hD : 0 < mu - t i := by linarith
  apply Set.Subset.antisymm
  · intro s hs
    have hzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → s r = 0 := by
      intro r hri hrj' hrk'
      exact hs.2 r (by simp [hri, hrj', hrk'])
    have hmassSum := sum_eq_add_add_of_zero_off_triple
      (fun r => s r) i j k hij hik hjk hzero
    have hmass : s i + s j + s k = 1 := by
      calc
        s i + s j + s k = ∑ r, s r := hmassSum.symm
        _ = 1 := hs.1.2.1
    have hmomSum := sum_eq_add_add_of_zero_off_triple
      (fun r => t r * s r) i j k hij hik hjk (by
        intro r hri hrj' hrk'
        change t r * s r = 0
        rw [hzero r hri hrj' hrk', mul_zero])
    have hmom : t i * s i + t j * s j + t k * s k = mu := by
      calc
        t i * s i + t j * s j + t k * s k = ∑ r, t r * s r := hmomSum.symm
        _ = mu := hs.1.2.2
    let A : ℝ := (t j - t i) * s j
    let B : ℝ := (t k - t i) * s k
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg hdj.le (hs.1.1 j)
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg hdk.le (hs.1.1 k)
    have hAB : A + B = mu - t i := by
      dsimp [A, B]
      linear_combination hmom - (t i) * hmass
    have hABpos : 0 < A + B := by rw [hAB]; exact hD
    have hα : 0 ≤ A / (A + B) := div_nonneg hA hABpos.le
    have hβ : 0 ≤ B / (A + B) := div_nonneg hB hABpos.le
    have hαβ : A / (A + B) + B / (A + B) = 1 := by
      rw [← add_div, div_self (ne_of_gt hABpos)]
    have hp : pairPoint t mu i j ∈ momentSlice t mu := pairPoint_mem t mu i j hli hrj
    have hq : pairPoint t mu i k ∈ momentSlice t mu := pairPoint_mem t mu i k hli hrk
    let v : EuclideanSpace ℝ (Fin n) :=
      (A / (A + B)) • pairPoint t mu i j +
        (B / (A + B)) • pairPoint t mu i k
    have hvP : v ∈ momentSlice t mu := by
      dsimp [v]
      exact (momentSlice_convex t mu) hp hq hα hβ hαβ
    have hvj : v j = s j := by
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i j j +
          (B / (A + B)) * pairPoint t mu i k j = s j
      rw [pairPoint_apply_right t mu i j hij,
        pairPoint_apply_other t mu i k j hji hjk, mul_zero, add_zero, hAB]
      dsimp [A]
      field_simp [ne_of_gt hD, ne_of_gt hdj]
    have hvk : v k = s k := by
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i j k +
          (B / (A + B)) * pairPoint t mu i k k = s k
      rw [pairPoint_apply_other t mu i j k hki hkj,
        pairPoint_apply_right t mu i k hik, mul_zero, zero_add, hAB]
      dsimp [B]
      field_simp [ne_of_gt hD, ne_of_gt hdk]
    have hvzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → v r = 0 := by
      intro r hri hrj' hrk'
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i j r +
          (B / (A + B)) * pairPoint t mu i k r = 0
      rw [pairPoint_apply_other t mu i j r hri hrj',
        pairPoint_apply_other t mu i k r hri hrk']
      ring
    have hvmassSum := sum_eq_add_add_of_zero_off_triple
      (fun r => v r) i j k hij hik hjk hvzero
    have hvmass : v i + v j + v k = 1 := by
      calc
        v i + v j + v k = ∑ r, v r := hvmassSum.symm
        _ = 1 := hvP.2.1
    have hvi : v i = s i := by
      nlinarith [hvmass, hmass, hvj, hvk]
    refine mem_segment_iff_div.mpr ⟨A, B, hA, hB, hABpos, ?_⟩
    change v = s
    ext r
    by_cases hri : r = i
    · subst r
      exact hvi
    · by_cases hrj' : r = j
      · subst r
        exact hvj
      · by_cases hrk' : r = k
        · subst r
          exact hvk
        · exact (hvzero r hri hrj' hrk').trans (hzero r hri hrj' hrk').symm
  · intro s hs
    have hpS : pairPoint t mu i j ∈ supportFace t mu {i, j, k} :=
      pairPoint_mem_supportFace t mu i j hli hrj {i, j, k} (by simp) (by simp)
    have hqS : pairPoint t mu i k ∈ supportFace t mu {i, j, k} :=
      pairPoint_mem_supportFace t mu i k hli hrk {i, j, k} (by simp) (by simp)
    exact segment_subset_supportFace t mu {i, j, k}
      (pairPoint t mu i j) (pairPoint t mu i k) hpS hqS hs

/-- Pair vertices sharing a low index are adjacent. -/
theorem pairPoint_adj_shared_low {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hli : t i < mu) (hrj : mu < t j) (hrk : mu < t k)
    (hjk : j ≠ k) :
    Adj (momentSlice t mu) (pairPoint t mu i j) (pairPoint t mu i k) := by
  classical
  have hij : i ≠ j := by intro h; subst j; linarith
  have hik : i ≠ k := by intro h; subst k; linarith
  have hji : j ≠ i := hij.symm
  have hne : pairPoint t mu i j ≠ pairPoint t mu i k := by
    intro h
    have hc := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s j) h
    change pairPoint t mu i j j = pairPoint t mu i k j at hc
    rw [pairPoint_apply_right t mu i j hij,
      pairPoint_apply_other t mu i k j hji hjk] at hc
    have hp : 0 < (mu - t i) / (t j - t i) := by
      exact div_pos (sub_pos.mpr hli) (sub_pos.mpr (hli.trans hrj))
    linarith
  refine ⟨hne, ?_⟩
  rw [← supportFace_triple_eq_segment_shared_low t mu i j k hli hrj hrk hjk]
  exact supportFace_isExtreme t mu {i, j, k}

/-- With two distinct low indices and one high index, the corresponding
three-coordinate support face is exactly the segment joining the two pair
vertices. -/
theorem supportFace_triple_eq_segment_shared_high {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hli : t i < mu) (hlj : t j < mu) (hrk : mu < t k)
    (hij : i ≠ j) :
    supportFace t mu {i, j, k} =
      segment ℝ (pairPoint t mu i k) (pairPoint t mu j k) := by
  classical
  have hik : i ≠ k := by
    intro h
    subst k
    linarith
  have hjk : j ≠ k := by
    intro h
    subst k
    linarith
  have hji : j ≠ i := hij.symm
  have hki : k ≠ i := hik.symm
  have hkj : k ≠ j := hjk.symm
  have hdi : 0 < t k - t i := by linarith
  have hdj : 0 < t k - t j := by linarith
  have hD : 0 < t k - mu := by linarith
  apply Set.Subset.antisymm
  · intro s hs
    have hzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → s r = 0 := by
      intro r hri hrj' hrk'
      exact hs.2 r (by simp [hri, hrj', hrk'])
    have hmassSum := sum_eq_add_add_of_zero_off_triple
      (fun r => s r) i j k hij hik hjk hzero
    have hmass : s i + s j + s k = 1 := by
      calc
        s i + s j + s k = ∑ r, s r := hmassSum.symm
        _ = 1 := hs.1.2.1
    have hmomSum := sum_eq_add_add_of_zero_off_triple
      (fun r => t r * s r) i j k hij hik hjk (by
        intro r hri hrj' hrk'
        change t r * s r = 0
        rw [hzero r hri hrj' hrk', mul_zero])
    have hmom : t i * s i + t j * s j + t k * s k = mu := by
      calc
        t i * s i + t j * s j + t k * s k = ∑ r, t r * s r := hmomSum.symm
        _ = mu := hs.1.2.2
    let A : ℝ := (t k - t i) * s i
    let B : ℝ := (t k - t j) * s j
    have hA : 0 ≤ A := by
      dsimp [A]
      exact mul_nonneg hdi.le (hs.1.1 i)
    have hB : 0 ≤ B := by
      dsimp [B]
      exact mul_nonneg hdj.le (hs.1.1 j)
    have hAB : A + B = t k - mu := by
      dsimp [A, B]
      linear_combination (t k) * hmass - hmom
    have hABpos : 0 < A + B := by rw [hAB]; exact hD
    have hα : 0 ≤ A / (A + B) := div_nonneg hA hABpos.le
    have hβ : 0 ≤ B / (A + B) := div_nonneg hB hABpos.le
    have hαβ : A / (A + B) + B / (A + B) = 1 := by
      rw [← add_div, div_self (ne_of_gt hABpos)]
    have hp : pairPoint t mu i k ∈ momentSlice t mu := pairPoint_mem t mu i k hli hrk
    have hq : pairPoint t mu j k ∈ momentSlice t mu := pairPoint_mem t mu j k hlj hrk
    let v : EuclideanSpace ℝ (Fin n) :=
      (A / (A + B)) • pairPoint t mu i k +
        (B / (A + B)) • pairPoint t mu j k
    have hvP : v ∈ momentSlice t mu := by
      dsimp [v]
      exact (momentSlice_convex t mu) hp hq hα hβ hαβ
    have hvi : v i = s i := by
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i k i +
          (B / (A + B)) * pairPoint t mu j k i = s i
      rw [pairPoint_apply_left,
        pairPoint_apply_other t mu j k i hij hik, mul_zero, add_zero, hAB]
      dsimp [A]
      field_simp [ne_of_gt hD, ne_of_gt hdi]
    have hvj : v j = s j := by
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i k j +
          (B / (A + B)) * pairPoint t mu j k j = s j
      rw [pairPoint_apply_other t mu i k j hji hjk,
        pairPoint_apply_left, mul_zero, zero_add, hAB]
      dsimp [B]
      field_simp [ne_of_gt hD, ne_of_gt hdj]
    have hvzero : ∀ r, r ≠ i → r ≠ j → r ≠ k → v r = 0 := by
      intro r hri hrj' hrk'
      dsimp [v]
      change
        (A / (A + B)) * pairPoint t mu i k r +
          (B / (A + B)) * pairPoint t mu j k r = 0
      rw [pairPoint_apply_other t mu i k r hri hrk',
        pairPoint_apply_other t mu j k r hrj' hrk']
      ring
    have hvmassSum := sum_eq_add_add_of_zero_off_triple
      (fun r => v r) i j k hij hik hjk hvzero
    have hvmass : v i + v j + v k = 1 := by
      calc
        v i + v j + v k = ∑ r, v r := hvmassSum.symm
        _ = 1 := hvP.2.1
    have hvk : v k = s k := by
      nlinarith [hvmass, hmass, hvi, hvj]
    refine mem_segment_iff_div.mpr ⟨A, B, hA, hB, hABpos, ?_⟩
    change v = s
    ext r
    by_cases hri : r = i
    · subst r
      exact hvi
    · by_cases hrj' : r = j
      · subst r
        exact hvj
      · by_cases hrk' : r = k
        · subst r
          exact hvk
        · exact (hvzero r hri hrj' hrk').trans (hzero r hri hrj' hrk').symm
  · intro s hs
    have hpS : pairPoint t mu i k ∈ supportFace t mu {i, j, k} :=
      pairPoint_mem_supportFace t mu i k hli hrk {i, j, k} (by simp) (by simp)
    have hqS : pairPoint t mu j k ∈ supportFace t mu {i, j, k} :=
      pairPoint_mem_supportFace t mu j k hlj hrk {i, j, k} (by simp) (by simp)
    exact segment_subset_supportFace t mu {i, j, k}
      (pairPoint t mu i k) (pairPoint t mu j k) hpS hqS hs

/-- Pair vertices sharing a high index are adjacent. -/
theorem pairPoint_adj_shared_high {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j k : Fin n)
    (hli : t i < mu) (hlj : t j < mu) (hrk : mu < t k)
    (hij : i ≠ j) :
    Adj (momentSlice t mu) (pairPoint t mu i k) (pairPoint t mu j k) := by
  classical
  have hik : i ≠ k := by intro h; subst k; linarith
  have hne : pairPoint t mu i k ≠ pairPoint t mu j k := by
    intro h
    have hc := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s i) h
    change pairPoint t mu i k i = pairPoint t mu j k i at hc
    rw [pairPoint_apply_left,
      pairPoint_apply_other t mu j k i hij hik] at hc
    have hp : 0 < (t k - mu) / (t k - t i) := by
      exact div_pos (sub_pos.mpr hrk) (sub_pos.mpr (hli.trans hrk))
    linarith
  refine ⟨hne, ?_⟩
  rw [← supportFace_triple_eq_segment_shared_high t mu i j k hli hlj hrk hij]
  exact supportFace_isExtreme t mu {i, j, k}

/-- Any two low/high pair vertices have a canonical route of at most two
edge/stay steps through the cross pair using the first low and second high
index. -/
theorem pairPoint_two_step_route {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ)
    (i k j l : Fin n)
    (hli : t i < mu) (hlk : t k < mu)
    (hrj : mu < t j) (hrl : mu < t l) :
    (pairPoint t mu i j = pairPoint t mu i l ∨
      Adj (momentSlice t mu) (pairPoint t mu i j) (pairPoint t mu i l)) ∧
    (pairPoint t mu i l = pairPoint t mu k l ∨
      Adj (momentSlice t mu) (pairPoint t mu i l) (pairPoint t mu k l)) := by
  constructor
  · by_cases hjl : j = l
    · left
      subst l
      rfl
    · right
      exact pairPoint_adj_shared_low t mu i j l hli hrj hrl hjl
  · by_cases hik : i = k
    · left
      subst k
      rfl
    · right
      exact pairPoint_adj_shared_high t mu i k l hli hlk hrl hik

#print axioms sum_eq_add_add_of_zero_off_triple
#print axioms supportFace_triple_eq_segment_shared_low
#print axioms pairPoint_adj_shared_low
#print axioms supportFace_triple_eq_segment_shared_high
#print axioms pairPoint_adj_shared_high
#print axioms pairPoint_two_step_route

end HirschExcessTwo

end

end

/- Frozen source: Solutions/PolynomialExcessTwoSingletonAdjacency.lean -/
section

/-!
# The missing edges incident to equal-moment singleton vertices

UNCOMPILED candidate continuation. No kernel or platform verdict is claimed.
Every proposed edge is proved via equality with a coordinate support face;
there is no inference from circuit status to graph adjacency.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschExcessTwo

lemma singletonPoint_mem_supportFace {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i : Fin n) (hi : t i = mu)
    (S : Finset (Fin n)) (hiS : i ∈ S) :
    singletonPoint i ∈ supportFace t mu S := by
  classical
  refine ⟨singletonPoint_mem t mu i hi, ?_⟩
  intro k hk
  have hki : k ≠ i := by intro h; subst k; exact hk hiS
  simp [singletonPoint_apply, hki]

/-- The support face on two distinct equal-moment coordinates is their segment. -/
theorem supportFace_pair_eq_segment_singletons {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hi : t i = mu) (hj : t j = mu) (hij : i ≠ j) :
    supportFace t mu {i, j} = segment ℝ (singletonPoint i) (singletonPoint j) := by
  classical
  apply Set.Subset.antisymm
  · intro s hs
    have hz : ∀ k, k ≠ i → k ≠ j → s k = 0 := by
      intro k hki hkj
      exact hs.2 k (by simp [hki, hkj])
    have hmass : s i + s j = 1 :=
      (sum_eq_add_of_zero_off_pair (fun k => s k) i j hij hz).symm.trans hs.1.2.1
    apply mem_segment_iff_div.mpr
    refine ⟨s i, s j, hs.1.1 i, hs.1.1 j, by linarith, ?_⟩
    simp only [hmass, div_one]
    ext k
    change s i * singletonPoint i k + s j * singletonPoint j k = s k
    by_cases hki : k = i
    · subst k
      simp [singletonPoint_apply, hij]
    · by_cases hkj : k = j
      · subst k
        simp [singletonPoint_apply, hij.symm]
      · simp [singletonPoint_apply, hki, hkj, hz k hki hkj]
  · exact segment_subset_supportFace t mu {i, j}
      (singletonPoint i) (singletonPoint j)
      (singletonPoint_mem_supportFace t mu i hi {i, j} (by simp))
      (singletonPoint_mem_supportFace t mu j hj {i, j} (by simp))

/-- Distinct equal-moment singleton vertices are joined by an actual edge. -/
theorem singletonPoint_adj_singletonPoint {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (i j : Fin n)
    (hi : t i = mu) (hj : t j = mu) (hij : i ≠ j) :
    Adj (momentSlice t mu) (singletonPoint i) (singletonPoint j) := by
  classical
  have hne : singletonPoint i ≠ singletonPoint j := by
    intro h
    have hc := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s i) h
    have hbad : (1 : ℝ) = 0 := by simpa [singletonPoint_apply, hij] using hc
    norm_num at hbad
  refine ⟨hne, ?_⟩
  rw [← supportFace_pair_eq_segment_singletons t mu i j hi hj hij]
  exact supportFace_isExtreme t mu {i, j}

/-- The carrier on one equal-moment coordinate and one low/high pair is exactly
the segment from the singleton to the pair vertex. The formula also handles
zero mass at either endpoint without division by that mass. -/
theorem supportFace_triple_eq_segment_singleton_pair {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (k i j : Fin n)
    (hk : t k = mu) (hli : t i < mu) (hrj : mu < t j) :
    supportFace t mu {k, i, j} =
      segment ℝ (singletonPoint k) (pairPoint t mu i j) := by
  classical
  have hki : k ≠ i := by intro h; subst k; linarith
  have hkj : k ≠ j := by intro h; subst k; linarith
  have hij : i ≠ j := by intro h; subst i; linarith
  have hden : 0 < t j - t i := sub_pos.mpr (hli.trans hrj)
  apply Set.Subset.antisymm
  · intro s hs
    have hz : ∀ r, r ≠ k → r ≠ i → r ≠ j → s r = 0 := by
      intro r hrk hri hrj'
      exact hs.2 r (by simp [hrk, hri, hrj'])
    have hmass : s k + s i + s j = 1 :=
      (sum_eq_add_add_of_zero_off_triple (fun r => s r) k i j
        hki hkj hij hz).symm.trans hs.1.2.1
    have hmom : mu * s k + t i * s i + t j * s j = mu := by
      have h := (sum_eq_add_add_of_zero_off_triple (fun r => t r * s r)
        k i j hki hkj hij (by
          intro r hrk hri hrj'
          change t r * s r = 0
          rw [hz r hrk hri hrj', mul_zero])).symm.trans hs.1.2.2
      simpa only [hk] using h
    have hsi : s i * (t j - t i) = (s i + s j) * (t j - mu) := by
      linear_combination mu * hmass - hmom
    have hsj : s j * (t j - t i) = (s i + s j) * (mu - t i) := by
      linear_combination hmom - mu * hmass
    have hsum : s k + (s i + s j) = 1 := by linarith
    apply mem_segment_iff_div.mpr
    refine ⟨s k, s i + s j, hs.1.1 k, add_nonneg (hs.1.1 i) (hs.1.1 j),
      by linarith, ?_⟩
    simp only [hsum, div_one]
    ext r
    change s k * singletonPoint k r + (s i + s j) * pairPoint t mu i j r = s r
    by_cases hrk : r = k
    · subst r
      rw [pairPoint_apply_other t mu i j k hki hkj]
      simp
    · by_cases hri : r = i
      · subst r
        simp only [singletonPoint_apply, if_neg hrk, mul_zero, zero_add,
          pairPoint_apply_left]
        calc
          (s i + s j) * ((t j - mu) / (t j - t i)) =
              ((s i + s j) * (t j - mu)) / (t j - t i) := by ring
          _ = s i := (div_eq_iff (ne_of_gt hden)).mpr hsi.symm
      · by_cases hrj' : r = j
        · subst r
          simp only [singletonPoint_apply, if_neg hrk, mul_zero, zero_add,
            pairPoint_apply_right t mu i j hij]
          calc
            (s i + s j) * ((mu - t i) / (t j - t i)) =
                ((s i + s j) * (mu - t i)) / (t j - t i) := by ring
            _ = s j := (div_eq_iff (ne_of_gt hden)).mpr hsj.symm
        · rw [pairPoint_apply_other t mu i j r hri hrj', hz r hrk hri hrj']
          simp [singletonPoint_apply, hrk]
  · exact segment_subset_supportFace t mu {k, i, j}
      (singletonPoint k) (pairPoint t mu i j)
      (singletonPoint_mem_supportFace t mu k hk {k, i, j} (by simp))
      (pairPoint_mem_supportFace t mu i j hli hrj {k, i, j} (by simp) (by simp))

/-- An equal-moment singleton is adjacent to every low/high pair vertex. -/
theorem singletonPoint_adj_pairPoint {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (k i j : Fin n)
    (hk : t k = mu) (hli : t i < mu) (hrj : mu < t j) :
    Adj (momentSlice t mu) (singletonPoint k) (pairPoint t mu i j) := by
  classical
  have hki : k ≠ i := by intro h; subst k; linarith
  have hkj : k ≠ j := by intro h; subst k; linarith
  have hne : singletonPoint k ≠ pairPoint t mu i j := by
    intro h
    have hc := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s k) h
    change singletonPoint k k = pairPoint t mu i j k at hc
    rw [pairPoint_apply_other t mu i j k hki hkj] at hc
    have hbad : (1 : ℝ) = 0 := by simpa using hc
    norm_num at hbad
  refine ⟨hne, ?_⟩
  rw [← supportFace_triple_eq_segment_singleton_pair t mu k i j hk hli hrj]
  exact supportFace_isExtreme t mu {k, i, j}

#print axioms supportFace_pair_eq_segment_singletons
#print axioms singletonPoint_adj_singletonPoint
#print axioms supportFace_triple_eq_segment_singleton_pair
#print axioms singletonPoint_adj_pairPoint

end HirschExcessTwo

end

end

/- Frozen source: Solutions/PolynomialExcessTwoDiameter.lean -/
section

/-!
# Full, support-preserving diameter two for the normalized moment slice

UNCOMPILED candidate. These declarations are not yet kernel-verified or
Prove2Me-published. No claim about a general H-polytope is made without an
additional affine slack-model equivalence.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace HirschExcessTwo

private lemma reverse_edge {E : Type*} [AddCommGroup E] [Module ℝ E]
    {P : Set E} {u v : E} (h : Adj P u v) : Adj P v u := by
  refine ⟨h.1.symm, ?_⟩
  simpa only [segment_symm] using h.2

/-- Complete two-step routing. The intermediate vertex preserves every
coordinate which is zero at both endpoints, so it remains in their common
coordinate support face. -/
theorem momentSlice_two_step_route_preserving_zeros {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ)
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ extremePoints ℝ (momentSlice t mu))
    (hy : y ∈ extremePoints ℝ (momentSlice t mu)) :
    ∃ z : EuclideanSpace ℝ (Fin n),
      z ∈ extremePoints ℝ (momentSlice t mu) ∧
      (x = z ∨ Adj (momentSlice t mu) x z) ∧
      (z = y ∨ Adj (momentSlice t mu) z y) ∧
      (∀ r, x r = 0 → y r = 0 → z r = 0) := by
  classical
  rcases (momentSlice_extremePoints_iff t mu x).mp hx with
    ⟨k, hk, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · rcases (momentSlice_extremePoints_iff t mu y).mp hy with
      ⟨l, hl, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
    · refine ⟨singletonPoint k, hx, Or.inl rfl, ?_, ?_⟩
      · by_cases hkl : k = l
        · subst l
          exact Or.inl rfl
        · exact Or.inr (singletonPoint_adj_singletonPoint t mu k l hk hl hkl)
      · intro r hr _
        exact hr
    · refine ⟨singletonPoint k, hx, Or.inl rfl,
        Or.inr (singletonPoint_adj_pairPoint t mu k i j hk hi hj), ?_⟩
      intro r hr _
      exact hr
  · rcases (momentSlice_extremePoints_iff t mu y).mp hy with
      ⟨k, hk, rfl⟩ | ⟨k, l, hk, hl, rfl⟩
    · refine ⟨singletonPoint k, hy,
        Or.inr (reverse_edge (singletonPoint_adj_pairPoint t mu k i j hk hi hj)),
        Or.inl rfl, ?_⟩
      intro r _ hr
      exact hr
    · obtain ⟨hfirst, hsecond⟩ := pairPoint_two_step_route t mu i k j l hi hk hj hl
      refine ⟨pairPoint t mu i l, pairPoint_mem_extremePoints t mu i l hi hl,
        hfirst, hsecond, ?_⟩
      intro r hx0 hy0
      have hir : r ≠ i := by
        intro h
        subst r
        have hp : 0 < pairPoint t mu i j i := by
          rw [pairPoint_apply_left]
          exact div_pos (sub_pos.mpr hj) (sub_pos.mpr (hi.trans hj))
        linarith
      have hlr : r ≠ l := by
        intro h
        subst r
        have hkl : k ≠ l := by intro h; subst l; linarith
        have hp : 0 < pairPoint t mu k l l := by
          rw [pairPoint_apply_right t mu k l hkl]
          exact div_pos (sub_pos.mpr hk) (sub_pos.mpr (hk.trans hl))
        linarith
      exact pairPoint_apply_other t mu i l r hir hlr

/-- The full theorem also applies inside each coordinate support face, with
edges of that face rather than merely ambient edges. -/
theorem supportFace_two_step_route {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n))
    (x y : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ extremePoints ℝ (supportFace t mu S))
    (hy : y ∈ extremePoints ℝ (supportFace t mu S)) :
    ∃ z : EuclideanSpace ℝ (Fin n),
      z ∈ extremePoints ℝ (supportFace t mu S) ∧
      (x = z ∨ Adj (supportFace t mu S) x z) ∧
      (z = y ∨ Adj (supportFace t mu S) z y) := by
  have hface := supportFace_isExtreme t mu S
  have hxP := hface.extremePoints_subset_extremePoints hx
  have hyP := hface.extremePoints_subset_extremePoints hy
  obtain ⟨z, hzP, hfirst, hsecond, hzeros⟩ :=
    momentSlice_two_step_route_preserving_zeros t mu x y hxP hyP
  have hzS : z ∈ supportFace t mu S := by
    refine ⟨hzP.1, ?_⟩
    intro r hr
    exact hzeros r (hx.1.2 r hr) (hy.1.2 r hr)
  have hz : z ∈ extremePoints ℝ (supportFace t mu S) :=
    inter_extremePoints_subset_extremePoints_of_subset
      (supportFace_subset t mu S) ⟨hzS, hzP⟩
  have restrict_edge : ∀ p q : EuclideanSpace ℝ (Fin n),
      p ∈ supportFace t mu S → q ∈ supportFace t mu S →
      Adj (momentSlice t mu) p q → Adj (supportFace t mu S) p q := by
    intro p q hp hq he
    exact ⟨he.1, he.2.mono (supportFace_subset t mu S)
      (segment_subset_supportFace t mu S p q hp hq)⟩
  refine ⟨z, hz, ?_, ?_⟩
  · rcases hfirst with heq | he
    · exact Or.inl heq
    · exact Or.inr (restrict_edge x z hx.1 hzS he)
  · rcases hsecond with heq | he
    · exact Or.inl heq
    · exact Or.inr (restrict_edge z y hzS hy.1 he)

private theorem diamLE_two_of_midpoints
    {E : Type*} [AddCommGroup E] [Module ℝ E] (P : Set E)
    (h : ∀ x ∈ extremePoints ℝ P, ∀ y ∈ extremePoints ℝ P,
      ∃ z : E, (x = z ∨ Adj P x z) ∧ (z = y ∨ Adj P z y)) : DiamLE P 2 := by
  intro x hx y hy
  obtain ⟨z, hxz, hzy⟩ := h x hx y hy
  refine ⟨fun k => if k = 0 then x else if k = 1 then z else y,
    by simp, by norm_num, ?_⟩
  intro k hk
  have hk01 : k = 0 ∨ k = 1 := by omega
  rcases hk01 with rfl | rfl
  · simpa using hxz
  · simpa using hzy

/-- Full normalized moment-slice graph diameter is at most two.
There are no genericity, dimension, nonemptiness, or strict-feasibility assumptions. -/
theorem momentSlice_diamLE_two {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) : DiamLE (momentSlice t mu) 2 := by
  apply diamLE_two_of_midpoints
  intro x hx y hy
  obtain ⟨z, _hz, hfirst, hsecond, _hzeros⟩ :=
    momentSlice_two_step_route_preserving_zeros t mu x y hx hy
  exact ⟨z, hfirst, hsecond⟩

/-- Every coordinate support face has intrinsic graph diameter at most two. -/
theorem supportFace_diamLE_two {n : ℕ}
    (t : Fin n → ℝ) (mu : ℝ) (S : Finset (Fin n)) :
    DiamLE (supportFace t mu S) 2 := by
  apply diamLE_two_of_midpoints
  intro x hx y hy
  obtain ⟨z, _hz, hfirst, hsecond⟩ := supportFace_two_step_route t mu S x y hx hy
  exact ⟨z, hfirst, hsecond⟩

#print axioms momentSlice_two_step_route_preserving_zeros
#print axioms supportFace_two_step_route
#print axioms momentSlice_diamLE_two
#print axioms supportFace_diamLE_two

end HirschExcessTwo

end

end

/- Frozen source: Solutions/PolynomialSlackMomentCertificate.lean -/
section

/-!
# Exact positive-slack certificates for two-moment normalization

The essential hypotheses are algebraic: an injective weighted row map, two
annihilating moments, and codimension two. No diameter bound is a hypothesis.
Existence of the positive normal relation for every bounded H-presentation is
not proved here. The exact image equality, unlike mere inclusion, justifies
transport of vertices, edges, and intrinsic row-support-face diameters.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschExcessTwo Module Submodule

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace HirschSlackMoment

/-- The mass and moment linear map on slack coordinates. -/
def momentMap {n : ℕ} (t : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (ℝ × ℝ) where
  toFun s := (∑ i, s i, ∑ i, t i * s i)
  map_add' x y := by
    apply Prod.ext
    · change (∑ i, (x i + y i)) = (∑ i, x i) + ∑ i, y i
      simp only [Finset.sum_add_distrib]
    · change (∑ i, t i * (x i + y i)) =
        (∑ i, t i * x i) + ∑ i, t i * y i
      simp only [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    apply Prod.ext
    · change (∑ i, r * x i) = r * ∑ i, x i
      exact (Finset.mul_sum _ _ _).symm
    · change (∑ i, t i * (r * x i)) = r * ∑ i, t i * x i
      calc
        _ = ∑ i, r * (t i * x i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := (Finset.mul_sum _ _ _).symm

@[simp] lemma momentMap_apply {n : ℕ}
    (t : Fin n → ℝ) (s : EuclideanSpace ℝ (Fin n)) :
    momentMap t s = (∑ i, s i, ∑ i, t i * s i) := rfl

lemma momentMap_singleton {n : ℕ} (t : Fin n → ℝ) (i : Fin n) :
    momentMap t (singletonPoint i) = (1, t i) := by
  have h := singletonPoint_mem t (t i) i rfl
  exact Prod.ext h.2.1 h.2.2

/-- Two different slopes make the two moment equations independent. -/
theorem momentMap_surjective {n : ℕ}
    (t : Fin n → ℝ) (ht : ∃ i j, t i ≠ t j) :
    Function.Surjective (momentMap t) := by
  obtain ⟨i, j, hij⟩ := ht
  have hden : t j - t i ≠ 0 := sub_ne_zero.mpr hij.symm
  rintro ⟨u, v⟩
  let A : ℝ := (t j * u - v) / (t j - t i)
  let B : ℝ := (v - t i * u) / (t j - t i)
  refine ⟨A • singletonPoint i + B • singletonPoint j, ?_⟩
  rw [map_add, map_smul, map_smul, momentMap_singleton, momentMap_singleton]
  apply Prod.ext
  · change A * 1 + B * 1 = u
    dsimp [A, B]
    field_simp [hden]
    ring
  · change A * t i + B * t j = v
    dsimp [A, B]
    field_simp [hden]
    ring

/-- Codimension, injectivity, and annihilation certify the WHOLE kernel. -/
theorem range_eq_moment_kernel_of_codimension_two {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (t : Fin n → ℝ) (hn : n = d + 2)
    (hL : Function.Injective L) (ht : ∃ i j, t i ≠ t j)
    (hzero : ∀ x, momentMap t (L x) = 0) :
    L.range = (momentMap t).ker := by
  have hsub : L.range ≤ (momentMap t).ker := by
    rintro y ⟨x, rfl⟩
    exact LinearMap.mem_ker.mpr (hzero x)
  have hdimL : Module.finrank ℝ L.range = d := by
    have h := L.finrank_range_add_finrank_ker
    rw [LinearMap.ker_eq_bot.mpr hL, finrank_bot, add_zero] at h
    simpa only [finrank_euclideanSpace_fin] using h
  have hdimM : Module.finrank ℝ (momentMap t).range = 2 := by
    rw [LinearMap.range_eq_top.mpr (momentMap_surjective t ht)]
    simp
  have hdimK : Module.finrank ℝ (momentMap t).ker = d := by
    have h := (momentMap t).finrank_range_add_finrank_ker
    rw [hdimM, finrank_euclideanSpace_fin] at h
    omega
  apply Submodule.eq_of_le_of_finrank_eq hsub
  rw [hdimL, hdimK]

/-- Affine offset minus the weighted row map. -/
def slackMap {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) :=
  AffineMap.const ℝ (EuclideanSpace ℝ (Fin d)) v - L.toAffineMap

@[simp] lemma slackMap_apply {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (x : EuclideanSpace ℝ (Fin d)) :
    slackMap L v x = v - L x := rfl

/-- The feasible set described by nonnegative affine slacks. -/
def slackPoly {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i, 0 ≤ (slackMap L v x) i}

theorem slackMap_injective {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (hL : Function.Injective L) :
    Function.Injective (slackMap L v) := by
  intro x y h
  apply hL
  have h' := congrArg (fun z => v - z) h
  simpa only [slackMap_apply, sub_sub_cancel] using h'

/-- Exact image, including every feasible point of the target moment slice. -/
theorem slackMap_image_eq_momentSlice {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ) (mu : ℝ)
    (hrange : L.range = (momentMap t).ker)
    (hv : momentMap t v = (1, mu)) :
    slackMap L v '' slackPoly L v = momentSlice t mu := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hLx : momentMap t (L x) = 0 := by
      apply LinearMap.mem_ker.mp
      rw [← hrange]
      exact ⟨x, rfl⟩
    have hm : momentMap t (slackMap L v x) = (1, mu) := by
      rw [slackMap_apply, map_sub, hLx, sub_zero, hv]
    exact ⟨hx, congrArg Prod.fst hm, congrArg Prod.snd hm⟩
  · intro hs
    have hm : momentMap t s = (1, mu) := Prod.ext hs.2.1 hs.2.2
    have hz : v - s ∈ L.range := by
      rw [hrange]
      apply LinearMap.mem_ker.mpr
      rw [map_sub, hv, hm, sub_self]
    obtain ⟨x, hx⟩ := hz
    have hfx : slackMap L v x = s := by
      rw [slackMap_apply, hx]
      abel
    refine ⟨x, ?_, hfx⟩
    intro i
    rw [hfx]
    exact hs.1 i

/-- Exact affine slack certificates transfer diameter two, without assuming
any local or global diameter bound. -/
theorem slackPoly_diamLE_two {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ) (mu : ℝ)
    (hL : Function.Injective L) (hrange : L.range = (momentMap t).ker)
    (hv : momentMap t v = (1, mu)) : DiamLE (slackPoly L v) 2 := by
  apply (Hirsch.affineMap_diamLE_image_iff_of_injective
    (slackMap L v) (slackMap_injective L v hL) (slackPoly L v) 2).mp
  rw [slackMap_image_eq_momentSlice L v t mu hrange hv]
  exact momentSlice_diamLE_two t mu

/-- A selected row-support face in original coordinates. -/
def slackSupportFace {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (S : Finset (Fin n)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | x ∈ slackPoly L v ∧ ∀ i, i ∉ S → (slackMap L v x) i = 0}

/-- Coordinate-zero support faces correspond exactly under the slack map. -/
theorem slackMap_image_supportFace {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ) (mu : ℝ)
    (hrange : L.range = (momentMap t).ker)
    (hv : momentMap t v = (1, mu)) (S : Finset (Fin n)) :
    slackMap L v '' slackSupportFace L v S = supportFace t mu S := by
  have himage := slackMap_image_eq_momentSlice L v t mu hrange hv
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, hx.2⟩
    rw [← himage]
    exact ⟨x, hx.1, rfl⟩
  · intro hs
    have hsimage : s ∈ slackMap L v '' slackPoly L v := by
      rw [himage]
      exact hs.1
    obtain ⟨x, hx, hfx⟩ := hsimage
    refine ⟨x, ⟨hx, ?_⟩, hfx⟩
    intro i hi
    rw [hfx]
    exact hs.2 i hi

/-- Intrinsic, not merely ambient, diameter of each row-support face. -/
theorem slackSupportFace_diamLE_two {d n : ℕ}
    (L : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (v : EuclideanSpace ℝ (Fin n)) (t : Fin n → ℝ) (mu : ℝ)
    (hL : Function.Injective L) (hrange : L.range = (momentMap t).ker)
    (hv : momentMap t v = (1, mu)) (S : Finset (Fin n)) :
    DiamLE (slackSupportFace L v S) 2 := by
  apply (Hirsch.affineMap_diamLE_image_iff_of_injective
    (slackMap L v) (slackMap_injective L v hL) (slackSupportFace L v S) 2).mp
  rw [slackMap_image_supportFace L v t mu hrange hv S]
  exact supportFace_diamLE_two t mu S

/-- Positive diagonal rescaling of the original row evaluation map. -/
def weightedRows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (c : Fin n → ℝ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun x := WithLp.toLp 2 (fun i => c i * ⟪a i, x⟫)
  map_add' x y := by
    ext i
    change c i * ⟪a i, x + y⟫ = c i * ⟪a i, x⟫ + c i * ⟪a i, y⟫
    rw [inner_add_right]
    ring
  map_smul' r x := by
    ext i
    change c i * ⟪a i, r • x⟫ = r * (c i * ⟪a i, x⟫)
    rw [inner_smul_right]
    ring

/-- Correspondingly scaled right-hand side. -/
def weightedOffset {n : ℕ} (b c : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => c i * b i)

lemma weighted_slack_apply {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    slackMap (weightedRows a c) (weightedOffset b c) x i =
      c i * (b i - ⟪a i, x⟫) := by
  change c i * b i - c i * ⟪a i, x⟫ = c i * (b i - ⟪a i, x⟫)
  ring

/-- Positive rescaling preserves the original inequalities exactly. -/
theorem slackPoly_weighted_eq_Hpoly {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) :
    slackPoly (weightedRows a c) (weightedOffset b c) = Hpoly a b := by
  ext x
  constructor
  · intro hx i
    have hi := hx i
    rw [weighted_slack_apply] at hi
    have hp : c i * ⟪a i, x⟫ ≤ c i * b i := by nlinarith only [hi]
    exact le_of_mul_le_mul_left hp (hc i)
  · intro hx i
    rw [weighted_slack_apply]
    exact mul_nonneg (hc i).le (sub_nonneg.mpr (hx i))

/-- Zero weighted slack means exactly original row tightness. -/
theorem weighted_slack_zero_iff {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    slackMap (weightedRows a c) (weightedOffset b c) x i = 0 ↔
      ⟪a i, x⟫ = b i := by
  rw [weighted_slack_apply]
  constructor
  · intro h
    have hz : b i - ⟪a i, x⟫ = 0 :=
      (mul_eq_zero.mp h).resolve_left (ne_of_gt (hc i))
    exact (sub_eq_zero.mp hz).symm
  · intro h
    rw [h, sub_self, mul_zero]

/-- A directly checkable codimension-two slack certificate gives the full
H-polytope diameter bound. All hypotheses concern linear algebra and positivity. -/
theorem hpoly_diamLE_two_of_positive_slack_certificate {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c t : Fin n → ℝ) (mu : ℝ)
    (hn : n = d + 2) (hc : ∀ i, 0 < c i)
    (hL : Function.Injective (weightedRows a c))
    (ht : ∃ i j, t i ≠ t j)
    (hzero : ∀ x, momentMap t (weightedRows a c x) = 0)
    (hoffset : momentMap t (weightedOffset b c) = (1, mu)) :
    DiamLE (Hpoly a b) 2 := by
  have hrange := range_eq_moment_kernel_of_codimension_two
    (weightedRows a c) t hn hL ht hzero
  have hdiam := slackPoly_diamLE_two
    (weightedRows a c) (weightedOffset b c) t mu hL hrange hoffset
  rw [slackPoly_weighted_eq_Hpoly a b c hc] at hdiam
  exact hdiam

/-- The same algebraic certificate bounds intrinsic diameters of arbitrary
selected original row-support faces. No ambient-only adjacency is substituted. -/
theorem row_support_diamLE_two_of_positive_slack_certificate {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c t : Fin n → ℝ) (mu : ℝ)
    (hn : n = d + 2) (hc : ∀ i, 0 < c i)
    (hL : Function.Injective (weightedRows a c))
    (ht : ∃ i j, t i ≠ t j)
    (hzero : ∀ x, momentMap t (weightedRows a c x) = 0)
    (hoffset : momentMap t (weightedOffset b c) = (1, mu))
    (S : Finset (Fin n)) :
    DiamLE {x | x ∈ Hpoly a b ∧ ∀ i, i ∉ S → ⟪a i, x⟫ = b i} 2 := by
  have hrange := range_eq_moment_kernel_of_codimension_two
    (weightedRows a c) t hn hL ht hzero
  have heq : slackSupportFace (weightedRows a c) (weightedOffset b c) S =
      {x | x ∈ Hpoly a b ∧ ∀ i, i ∉ S → ⟪a i, x⟫ = b i} := by
    ext x
    simp only [slackSupportFace, Set.mem_setOf_eq,
      slackPoly_weighted_eq_Hpoly a b c hc, weighted_slack_zero_iff a b c hc]
  rw [← heq]
  exact slackSupportFace_diamLE_two
    (weightedRows a c) (weightedOffset b c) t mu hL hrange hoffset S

#print axioms momentMap_surjective
#print axioms range_eq_moment_kernel_of_codimension_two
#print axioms slackMap_injective
#print axioms slackMap_image_eq_momentSlice
#print axioms slackPoly_diamLE_two
#print axioms slackMap_image_supportFace
#print axioms slackSupportFace_diamLE_two
#print axioms slackPoly_weighted_eq_Hpoly
#print axioms weighted_slack_zero_iff
#print axioms hpoly_diamLE_two_of_positive_slack_certificate
#print axioms row_support_diamLE_two_of_positive_slack_certificate

end HirschSlackMoment

end

end

/- Frozen source: Solutions/PolynomialVertexSpan.lean -/
section

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000

namespace HirschPolynomialAccess

/-- A direct finite-perturbation proof, with no imported theorem stubs.
A direction annihilating all inequalities active at a vertex must be zero. -/
theorem vertex_tight_rows_span_checked
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (y : EuclideanSpace ℝ (Fin d))
    (horth : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    y = 0 := by
  classical
  have hlocal : ∀ i : Fin n, ∃ t : ℝ,
      0 < t ∧ t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [horth i hi, abs_zero, mul_zero, hi, sub_self]
    · have hs : 0 < b i - ⟪a i, x⟫ := sub_pos.mpr (lt_of_le_of_ne (hx.1 i) hi)
      have hd : 0 < |⟪a i, y⟫| + 1 := by positivity
      let t : ℝ := (b i - ⟪a i, x⟫) / (|⟪a i, y⟫| + 1)
      have ht : 0 < t := div_pos hs hd
      have hprod : t * (|⟪a i, y⟫| + 1) = b i - ⟪a i, x⟫ := by
        dsimp [t]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      exact ⟨t, ht, by nlinarith⟩
  choose e hepos hebound using hlocal
  have huniform : ∀ S : Finset (Fin n), ∃ t : ℝ,
      0 < t ∧ ∀ i ∈ S, t ≤ e i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨t, ht, hti⟩ := ih
      refine ⟨min (e i) t, lt_min (hepos i) ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (hti j hjS)
  obtain ⟨t, ht, hte⟩ := huniform Finset.univ
  have hbudget : ∀ i, t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    exact (mul_le_mul_of_nonneg_right (hte i (Finset.mem_univ i))
      (abs_nonneg _)).trans (hebound i)
  have hp : x + t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (le_abs_self ⟪a i, y⟫) ht.le
    rw [inner_add_right, inner_smul_right]
    linarith [hbudget i]
  have hm : x - t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (neg_le_abs ⟪a i, y⟫) ht.le
    rw [mul_neg] at hmul
    rw [inner_sub_right, inner_smul_right]
    linarith [hbudget i]
  have hmid : x ∈ openSegment ℝ (x + t • y) (x - t • y) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num,
      by norm_num, ?_⟩
    module
  have hpeq : x + t • y = x := hx.2 hp hm hmid
  have hty : t • y = 0 := by
    have h := congrArg (fun z => z - x) hpeq
    simpa using h
  exact (smul_eq_zero.mp hty).resolve_left (ne_of_gt ht)

#print axioms vertex_tight_rows_span_checked

end HirschPolynomialAccess

end

/- Frozen source: Solutions/PolynomialSlackNormalRelations.lean -/
section

/-!
# Finite normal-relation witnesses for the excess-two slack model

A reference extreme vertex supplies injectivity. Two finite vector identities
supply the annihilating moments. All certificate data are ordinary real vectors
and scalars; no carrier diameter or unknown theorem is a hypothesis.

Existence of these relation witnesses from boundedness alone is separate work.
-/

open scoped BigOperators RealInnerProductSpace
open Set Hirsch HirschExcessTwo

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace HirschSlackMoment

/-- Any positive diagonal row scaling remains injective when the original
H-polyhedron has an extreme vertex. -/
theorem weightedRows_injective_of_extremePoint {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c : Fin n → ℝ)
    (hc : ∀ i, 0 < c i) (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b)) :
    Function.Injective (weightedRows a c) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b z hz (x - y)
  intro i _
  have hi := congrArg (fun s : EuclideanSpace ℝ (Fin n) => s i) hxy
  change c i * ⟪a i, x⟫ = c i * ⟪a i, y⟫ at hi
  have heq : ⟪a i, x⟫ = ⟪a i, y⟫ := mul_left_cancel₀ (ne_of_gt (hc i)) hi
  rw [inner_sub_right, heq, sub_self]

lemma weighted_normal_relation_eval {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (c : Fin n → ℝ)
    (hrel : (∑ i, c i • a i) = 0) (x : EuclideanSpace ℝ (Fin d)) :
    (∑ i, c i * ⟪a i, x⟫) = 0 := by
  have h := congrArg (fun y : EuclideanSpace ℝ (Fin d) => ⟪y, x⟫) hrel
  simpa only [sum_inner, real_inner_smul_left, inner_zero_left] using h

/-- Two finite vector relations imply both moments annihilate every row-map
image. The right-hand sides are not involved in this direction-space fact. -/
theorem normal_relations_annihilate_weightedRows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (c t : Fin n → ℝ)
    (hfirst : (∑ i, c i • a i) = 0)
    (hsecond : (∑ i, (t i * c i) • a i) = 0) :
    ∀ x, momentMap t (weightedRows a c x) = 0 := by
  intro x
  apply Prod.ext
  · change (∑ i, c i * ⟪a i, x⟫) = 0
    exact weighted_normal_relation_eval a c hfirst x
  · change (∑ i, t i * (c i * ⟪a i, x⟫)) = 0
    simpa only [mul_assoc] using
      weighted_normal_relation_eval a (fun i => t i * c i) hsecond x

/-- A normalized positive normal relation, an independent second relation,
and a reference vertex provide the complete geometric diameter certificate.
The conclusion simultaneously covers every original row-support face. -/
theorem hpoly_and_row_faces_diamLE_two_of_normal_relations {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c t : Fin n → ℝ)
    (hn : n = d + 2) (hc : ∀ i, 0 < c i)
    (ht : ∃ i j, t i ≠ t j)
    (hfirst : (∑ i, c i • a i) = 0)
    (hsecond : (∑ i, (t i * c i) • a i) = 0)
    (hmass : (∑ i, c i * b i) = 1)
    (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b)) :
    DiamLE (Hpoly a b) 2 ∧
      ∀ S : Finset (Fin n),
        DiamLE {x | x ∈ Hpoly a b ∧ ∀ i, i ∉ S → ⟪a i, x⟫ = b i} 2 := by
  let mu : ℝ := ∑ i, t i * (c i * b i)
  have hL := weightedRows_injective_of_extremePoint a b c hc z hz
  have hzero := normal_relations_annihilate_weightedRows a c t hfirst hsecond
  have hoffset : momentMap t (weightedOffset b c) = (1, mu) := by
    apply Prod.ext
    · exact hmass
    · rfl
  refine ⟨hpoly_diamLE_two_of_positive_slack_certificate
    a b c t mu hn hc hL ht hzero hoffset, ?_⟩
  intro S
  exact row_support_diamLE_two_of_positive_slack_certificate
    a b c t mu hn hc hL ht hzero hoffset S

#print axioms weightedRows_injective_of_extremePoint
#print axioms normal_relations_annihilate_weightedRows
#print axioms hpoly_and_row_faces_diamLE_two_of_normal_relations

end HirschSlackMoment

end

end

open scoped BigOperators RealInnerProductSpace
open Set Hirsch

theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b c t : Fin n → ℝ)
    (hn : n = d + 2) (hc : ∀ i, 0 < c i)
    (ht : ∃ i j, t i ≠ t j)
    (hfirst : (∑ i, c i • a i) = 0)
    (hsecond : (∑ i, (t i * c i) • a i) = 0)
    (hmass : (∑ i, c i * b i) = 1)
    (z : EuclideanSpace ℝ (Fin d))
    (hz : z ∈ extremePoints ℝ (Hpoly a b)) :
    DiamLE (Hpoly a b) 2 ∧
      ∀ S : Finset (Fin n),
        DiamLE {x | x ∈ Hpoly a b ∧ ∀ i, i ∉ S → ⟪a i, x⟫ = b i} 2 := by
  exact HirschSlackMoment.hpoly_and_row_faces_diamLE_two_of_normal_relations
    a b c t hn hc ht hfirst hsecond hmass z hz

#print axioms solution
