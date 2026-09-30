-- Prove2me | solution 1 for Hirsch.hpoly_diameter_le_excess_of_independent_small_row_blocks
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T20:34:54.272447+00:00
-- url     : https://prove2.me/submissions/78085f91-e27d-4a2d-90ed-5c646a38f8ae

import Theorems.Thm_Hirsch_hpoly_diameter_le_excess_of_rows_le_dim_add_three
import Mathlib
import Definitions.Def_Hirsch_model
open scoped BigOperators RealInnerProductSpace
open Set Hirsch


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

/-- A high-excess parent is Hirsch-bounded when each algebraically independent
row block has excess at most three. The only imported diameter input is the
already-proved low-excess H-polyhedron theorem, supplied explicitly so no
platform theorem stub or unproved global claim enters the axiom closure.
There is NO restriction on total `n-d` or on the number of factors. -/
theorem hpoly_diamLE_excess_of_small_row_blocks
    (hsmall : ∀ {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d))
      (b : Fin n → ℝ), Bornology.IsBounded (Hpoly a b) →
      n ≤ d + 3 → DiamLE (Hpoly a b) (n - d))
    {d n k : ℕ} (dims counts : Fin k → ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (T : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ]
      (∀ i : Fin k, EuclideanSpace ℝ (Fin (dims i))))
    (e : (Σ i : Fin k, Fin (counts i)) ≃ Fin n)
    (A : ∀ i : Fin k, Fin (counts i) → EuclideanSpace ℝ (Fin (dims i)))
    (hrows : ∀ z i j, ⟪a (e ⟨i, j⟩), T.symm z⟫ = ⟪A i j, z i⟫)
    (hbd : Bornology.IsBounded (Hpoly a b)) (hne : (Hpoly a b).Nonempty)
    (hcount : ∀ i, dims i ≤ counts i)
    (hsmallcount : ∀ i, counts i ≤ dims i + 3) :
    DiamLE (Hpoly a b) (n - d) := by
  have hfactorbd := factors_bounded_of_row_blocks dims counts a b T e A hrows hbd hne
  have hD := HirschProduct.diamLE_pi
    (fun i => Hpoly (A i) (fun j => b (e ⟨i, j⟩)))
    (fun i => counts i - dims i)
    (fun i => hsmall (A i) (fun j => b (e ⟨i, j⟩)) (hfactorbd i) (hsmallcount i))
  rw [row_block_excess_sum dims counts T e hcount] at hD
  rw [← image_hpoly_eq_pi_of_row_blocks dims counts a b T e A hrows] at hD
  exact (Hirsch.affineEquiv_diamLE_image_iff T.toAffineEquiv (Hpoly a b) (n - d)).mp hD


end HirschRowBlocks


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
    (hsmallcount : ∀ i, counts i ≤ dims i + 3) :
    DiamLE (Hpoly a b) (n - d) := by
  exact HirschRowBlocks.hpoly_diamLE_excess_of_small_row_blocks
    (fun {d n} a b hbd hrows =>
      Hirsch.hpoly_diameter_le_excess_of_rows_le_dim_add_three d n a b hrows hbd)
      dims counts a b T e A hrows hbd hne hcount hsmallcount

#print axioms solution
