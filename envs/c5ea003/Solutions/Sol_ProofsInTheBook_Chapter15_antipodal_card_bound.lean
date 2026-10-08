-- Prove2me | solution 1 for ProofsInTheBook.Chapter15.antipodal_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T15:41:30.214756+00:00
-- url     : https://prove2.me/submissions/77e91fac-25b2-4b01-aede-0d7b2ed3759c

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter15


/-!
# Chapter 15: Every large point set has an obtuse angle

The book statement is the Danzer-Grünbaum theorem: any set of more than `2^d`
points in `ℝ^d` contains three points forming an obtuse angle.

Intended Lean theorem: for `points : Finset (EuclideanSpace ℝ (Fin d))`,
`2^d < points.card` should imply that three points of `points` make an obtuse
angle, expressed by a negative inner product.

Formalization status (playbook point 17): status ①. The reduction from the
no-obtuse-angle condition to the antipodal/supporting-strip condition is
formalized below. The Klee packing geometry is formalized through the
half-sized convex-hull copies: they lie inside the original convex hull, have
volume `2^{-d}` times the hull volume, and are pairwise a.e.-disjoint. The
zero ambient-volume case is discharged by reducing to the affine span of the
point set and reapplying the same antipodal bound in that smaller Euclidean
space.

This file intentionally does not contain the old sign-vector pigeonhole theorem:
there is no assumed `sign` map and no assumed injectivity.
-/

namespace ProofsInTheBook.Chapter15

open scoped ENNReal RealInnerProductSpace
open MeasureTheory

noncomputable section



















theorem mem_separatingHyperplane {d : ℕ} {a b y : Point d} :
    y ∈ (SeparatingHyperplane a b : Set (Point d)) ↔
      ⟪b - a, y - KleeMidpoint a b⟫ = 0 := by
  rw [SeparatingHyperplane]
  change y - KleeMidpoint a b ∈
      LinearMap.ker ((innerSL ℝ (b - a) : Point d →L[ℝ] ℝ) : Point d →ₗ[ℝ] ℝ) ↔
    ⟪b - a, y - KleeMidpoint a b⟫ = 0
  rw [LinearMap.mem_ker]
  constructor <;> intro h <;> simpa [inner_sub_left, real_inner_comm] using h

theorem separatingHyperplane_ne_top {d : ℕ} {a b : Point d} (hab : a ≠ b) :
    SeparatingHyperplane a b ≠ ⊤ := by
  intro htop
  have hv_mem : b - a ∈ (SeparatingHyperplane a b).direction := by
    rw [htop]
    simp
  have hv_ker : b - a ∈ LinearMap.ker
      ((innerSL ℝ (b - a) : Point d →L[ℝ] ℝ) : Point d →ₗ[ℝ] ℝ) := by
    simpa [SeparatingHyperplane] using hv_mem
  have hv_apply := LinearMap.mem_ker.mp hv_ker
  have hv_inner : ⟪b - a, b - a⟫ = 0 := by
    change (innerSL ℝ (b - a) : Point d →L[ℝ] ℝ) (b - a) = 0 at hv_apply
    simpa only [innerSL_apply_apply, real_inner_comm] using hv_apply
  have hv_zero : b - a = 0 := inner_self_eq_zero.mp hv_inner
  exact hab (eq_of_sub_eq_zero hv_zero).symm

theorem stripHalfspaceLeft_convex {d : ℕ} (a b : Point d) :
    Convex ℝ {x : Point d | 0 ≤ ⟪b - a, x - a⟫} := by
  convert convex_halfSpace_ge (E := Point d) (β := ℝ) (𝕜 := ℝ)
    ((innerSL ℝ (b - a)).isLinear) (⟪b - a, a⟫) using 1
  ext x
  simp [inner_sub_right, inner_sub_left, real_inner_comm, sub_nonneg]

theorem inPerpendicularStrip_convex {d : ℕ} (a b : Point d) :
    Convex ℝ {x : Point d | InPerpendicularStrip a b x} := by
  change Convex ℝ ({x : Point d | 0 ≤ ⟪b - a, x - a⟫} ∩
    {x : Point d | 0 ≤ ⟪a - b, x - b⟫})
  exact (stripHalfspaceLeft_convex a b).inter (stripHalfspaceLeft_convex b a)

theorem HasAntipodalStrips.convexHull_subset_strip {d : ℕ}
    {points : Finset (Point d)} (hanti : HasAntipodalStrips points)
    {a b : Point d} (ha : a ∈ points) (hb : b ∈ points) (hab : a ≠ b) :
    convexHull ℝ (points : Set (Point d)) ⊆ {x : Point d | InPerpendicularStrip a b x} := by
  exact convexHull_min (fun x hx => hanti a ha b hb hab x hx) (inPerpendicularStrip_convex a b)

theorem KleeCopy.subset_convexHull {d : ℕ} {points : Finset (Point d)} {p : Point d}
    (hp : p ∈ points) : KleeCopy points p ⊆ convexHull ℝ (points : Set (Point d)) := by
  rintro y ⟨x, hx, rfl⟩
  have hp' : p ∈ convexHull ℝ (points : Set (Point d)) := _root_.subset_convexHull ℝ _ hp
  simpa [KleeCopy, smul_add] using
    (convex_convexHull ℝ (points : Set (Point d))) hp' hx
      (by norm_num : 0 ≤ (2 : ℝ)⁻¹) (by norm_num : 0 ≤ (2 : ℝ)⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ + (2 : ℝ)⁻¹ = 1)

theorem KleeCopy.eq_homothety {d : ℕ} (points : Finset (Point d)) (p : Point d) :
    KleeCopy points p =
      AffineMap.homothety p ((2 : ℝ)⁻¹) '' convexHull ℝ (points : Set (Point d)) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp [AffineMap.homothety_apply]
    module
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp [AffineMap.homothety_apply]
    module

theorem KleeCopy.convex {d : ℕ} (points : Finset (Point d)) (p : Point d) :
    Convex ℝ (KleeCopy points p) := by
  rw [KleeCopy.eq_homothety]
  exact (convex_convexHull ℝ (points : Set (Point d))).affine_image _

theorem KleeCopy.nullMeasurableSet {d : ℕ} (points : Finset (Point d)) (p : Point d) :
    NullMeasurableSet (KleeCopy points p) volume :=
  (KleeCopy.convex points p).nullMeasurableSet volume

theorem KleeCopy.volume_eq {d : ℕ} (points : Finset (Point d)) (p : Point d) :
    volume (KleeCopy points p) = ENNReal.ofReal ((2 : ℝ)⁻¹ ^ d) *
      volume (convexHull ℝ (points : Set (Point d))) := by
  rw [KleeCopy.eq_homothety]
  rw [Measure.addHaar_image_homothety]
  simp

theorem KleeCopy.left_separated {d : ℕ} {points : Finset (Point d)}
    (hanti : HasAntipodalStrips points) {a b : Point d}
    (ha : a ∈ points) (hb : b ∈ points) (hab : a ≠ b) :
    KleeCopy points a ⊆ {y : Point d | ⟪b - a, y - KleeMidpoint a b⟫ ≤ 0} := by
  rintro y ⟨x, hx, rfl⟩
  have hxstrip : InPerpendicularStrip a b x :=
    hanti.convexHull_subset_strip ha hb hab hx
  have hle : ⟪b - a, x - b⟫ ≤ 0 := by
    have hneg : ⟪b - a, x - b⟫ = -⟪a - b, x - b⟫ := by
      rw [show b - a = -(a - b) by abel, inner_neg_left]
    rw [hneg]
    exact neg_nonpos.2 hxstrip.2
  rw [KleeMidpoint]
  calc
    ⟪b - a, (2 : ℝ)⁻¹ • (a + x) - (2 : ℝ)⁻¹ • (a + b)⟫ =
        (2 : ℝ)⁻¹ * ⟪b - a, x - b⟫ := by
      simp [sub_eq_add_neg, inner_add_right, inner_smul_right]
      ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hle

theorem KleeCopy.right_separated {d : ℕ} {points : Finset (Point d)}
    (hanti : HasAntipodalStrips points) {a b : Point d}
    (ha : a ∈ points) (hb : b ∈ points) (hab : a ≠ b) :
    KleeCopy points b ⊆ {y : Point d | 0 ≤ ⟪b - a, y - KleeMidpoint a b⟫} := by
  rintro y ⟨x, hx, rfl⟩
  have hxstrip : InPerpendicularStrip a b x :=
    hanti.convexHull_subset_strip ha hb hab hx
  rw [KleeMidpoint]
  calc
    0 ≤ (2 : ℝ)⁻¹ * ⟪b - a, x - a⟫ := by
      exact mul_nonneg (by positivity) hxstrip.1
    _ = ⟪b - a, (2 : ℝ)⁻¹ • (b + x) - (2 : ℝ)⁻¹ • (a + b)⟫ := by
      simp [sub_eq_add_neg, inner_add_right, inner_smul_right]
      ring

theorem KleeCopy.inter_subset_separatingHyperplane {d : ℕ}
    {points : Finset (Point d)} (hanti : HasAntipodalStrips points)
    {a b : Point d} (ha : a ∈ points) (hb : b ∈ points) (hab : a ≠ b) :
    KleeCopy points a ∩ KleeCopy points b ⊆ SeparatingHyperplane a b := by
  intro y hy
  rw [mem_separatingHyperplane]
  exact le_antisymm (KleeCopy.left_separated hanti ha hb hab hy.1)
    (KleeCopy.right_separated hanti ha hb hab hy.2)

theorem KleeCopy.aedisjoint {d : ℕ} {points : Finset (Point d)}
    (hanti : HasAntipodalStrips points) {a b : Point d}
    (ha : a ∈ points) (hb : b ∈ points) (hab : a ≠ b) :
    AEDisjoint MeasureTheory.volume (KleeCopy points a) (KleeCopy points b) := by
  rw [AEDisjoint]
  exact measure_mono_null (KleeCopy.inter_subset_separatingHyperplane hanti ha hb hab)
    (Measure.addHaar_affineSubspace MeasureTheory.volume (SeparatingHyperplane a b)
      (separatingHyperplane_ne_top hab))

theorem KleeCopy.sum_volume_le_volume_convexHull {d : ℕ} {points : Finset (Point d)}
    (hanti : HasAntipodalStrips points) :
    (∑ p ∈ points, MeasureTheory.volume (KleeCopy points p)) ≤
      MeasureTheory.volume (convexHull ℝ (points : Set (Point d))) := by
  have hpw : (points : Set (Point d)).Pairwise
      (Function.onFun (AEDisjoint MeasureTheory.volume) fun p => KleeCopy points p) := by
    intro a ha b hb hab
    exact KleeCopy.aedisjoint hanti ha hb hab
  have hm : ∀ p ∈ points, NullMeasurableSet (KleeCopy points p) MeasureTheory.volume := by
    intro p _hp
    exact KleeCopy.nullMeasurableSet points p
  have hunion_subset : (⋃ p ∈ points, KleeCopy points p) ⊆
      convexHull ℝ (points : Set (Point d)) := by
    intro y hy
    rcases Set.mem_iUnion.1 hy with ⟨p, hyp⟩
    rcases Set.mem_iUnion.1 hyp with ⟨hp, hycopy⟩
    exact KleeCopy.subset_convexHull hp hycopy
  calc
    (∑ p ∈ points, MeasureTheory.volume (KleeCopy points p)) =
        MeasureTheory.volume (⋃ p ∈ points, KleeCopy points p) := by
      exact (measure_biUnion_finset₀ hpw hm).symm
    _ ≤ MeasureTheory.volume (convexHull ℝ (points : Set (Point d))) :=
      measure_mono hunion_subset

theorem convexHull_volume_ne_top {d : ℕ} (points : Finset (Point d)) :
    MeasureTheory.volume (convexHull ℝ (points : Set (Point d))) ≠ ∞ := by
  have hcompact : IsCompact (convexHull ℝ (points : Set (Point d))) := by
    set_option synthInstance.maxHeartbeats 80000 in
    exact Set.Finite.isCompact_convexHull ℝ (s := (points : Set (Point d))) points.finite_toSet
  exact hcompact.measure_ne_top

theorem antipodal_card_bound_of_positive_volume {d : ℕ} {points : Finset (Point d)}
    (hanti : HasAntipodalStrips points)
    (hvol0 : MeasureTheory.volume (convexHull ℝ (points : Set (Point d))) ≠ 0) :
    points.card ≤ 2 ^ d := by
  let μ : ℝ≥0∞ := MeasureTheory.volume (convexHull ℝ (points : Set (Point d)))
  let c : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ)⁻¹ ^ d)
  have hsum := KleeCopy.sum_volume_le_volume_convexHull hanti
  have hsum' : (points.card : ℝ≥0∞) * (c * μ) ≤ μ := by
    subst c
    subst μ
    simpa only [KleeCopy.volume_eq, Finset.sum_const, nsmul_eq_mul] using hsum
  have hcancel : (points.card : ℝ≥0∞) * c ≤ 1 := by
    rw [← ENNReal.mul_le_mul_iff_left hvol0 (convexHull_volume_ne_top points)]
    simpa [μ, mul_assoc, mul_left_comm, mul_comm] using hsum'
  have hreal : ((points.card : ℝ≥0∞) * c).toReal ≤ (1 : ℝ≥0∞).toReal :=
    ENNReal.toReal_mono (by finiteness) hcancel
  have hreal' : (points.card : ℝ) * ((2 : ℝ)⁻¹ ^ d) ≤ 1 := by
    simpa [c, ENNReal.toReal_ofReal (pow_nonneg (by norm_num : 0 ≤ (2 : ℝ)⁻¹) d)] using hreal
  have hreal_bound : (points.card : ℝ) ≤ (2 : ℝ) ^ d := by
    calc
      (points.card : ℝ) = (points.card : ℝ) * 1 := by ring
      _ = (points.card : ℝ) * (((2 : ℝ)⁻¹ ^ d) * (2 : ℝ) ^ d) := by
        rw [← mul_pow, inv_mul_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow]
      _ = ((points.card : ℝ) * ((2 : ℝ)⁻¹ ^ d)) * (2 : ℝ) ^ d := by ring
      _ ≤ 1 * (2 : ℝ) ^ d := by
        exact mul_le_mul_of_nonneg_right hreal' (by positivity)
      _ = (2 : ℝ) ^ d := by ring
  exact Nat.cast_le.mp (by
    exact_mod_cast hreal_bound : (points.card : ℝ) ≤ ((2 ^ d : ℕ) : ℝ))



theorem affineSpanCoord_inner_eq {d : ℕ} {points : Finset (Point d)}
    {p0 a b x : Point d}
    (hp0A : p0 ∈ affineSpan ℝ (points : Set (Point d)))
    (haA : a ∈ affineSpan ℝ (points : Set (Point d)))
    (hbA : b ∈ affineSpan ℝ (points : Set (Point d)))
    (hxA : x ∈ affineSpan ℝ (points : Set (Point d))) :
    ⟪affineSpanCoord points p0 hp0A b - affineSpanCoord points p0 hp0A a,
      affineSpanCoord points p0 hp0A x - affineSpanCoord points p0 hp0A a⟫ =
      ⟪b - a, x - a⟫ := by
  let A := affineSpan ℝ (points : Set (Point d))
  let W := A.direction
  let e := (stdOrthonormalBasis ℝ W).repr
  let va : W := ⟨a - p0, A.vsub_mem_direction haA hp0A⟩
  let vb : W := ⟨b - p0, A.vsub_mem_direction hbA hp0A⟩
  let vx : W := ⟨x - p0, A.vsub_mem_direction hxA hp0A⟩
  have haCoord : affineSpanCoord points p0 hp0A a = e va := by
    simp [affineSpanCoord, A, W, e, va, haA]
  have hbCoord : affineSpanCoord points p0 hp0A b = e vb := by
    simp [affineSpanCoord, A, W, e, vb, hbA]
  have hxCoord : affineSpanCoord points p0 hp0A x = e vx := by
    simp [affineSpanCoord, A, W, e, vx, hxA]
  rw [haCoord, hbCoord, hxCoord]
  calc
    ⟪e vb - e va, e vx - e va⟫ = ⟪e (vb - va), e (vx - va)⟫ := by simp
    _ = ⟪vb - va, vx - va⟫ := by rw [LinearIsometryEquiv.inner_map_map]
    _ = ⟪b - a, x - a⟫ := by
      rw [Submodule.coe_inner]
      change ⟪((vb - va : W) : Point d), ((vx - va : W) : Point d)⟫ =
        ⟪b - a, x - a⟫
      simp [va, vb, vx]

theorem affineSpanCoord_injOn {d : ℕ} {points : Finset (Point d)} {p0 : Point d}
    (hp0A : p0 ∈ affineSpan ℝ (points : Set (Point d))) :
    Set.InjOn (affineSpanCoord points p0 hp0A) (points : Set (Point d)) := by
  intro x hx y hy hxy
  let A := affineSpan ℝ (points : Set (Point d))
  let W := A.direction
  let e := (stdOrthonormalBasis ℝ W).repr
  have hxA : x ∈ A := subset_affineSpan ℝ (points : Set (Point d)) hx
  have hyA : y ∈ A := subset_affineSpan ℝ (points : Set (Point d)) hy
  let vx : W := ⟨x - p0, A.vsub_mem_direction hxA hp0A⟩
  let vy : W := ⟨y - p0, A.vsub_mem_direction hyA hp0A⟩
  have hxCoord : affineSpanCoord points p0 hp0A x = e vx := by
    simp [affineSpanCoord, A, W, e, vx, hxA]
  have hyCoord : affineSpanCoord points p0 hp0A y = e vy := by
    simp [affineSpanCoord, A, W, e, vy, hyA]
  have hxy' : e vx = e vy := by simpa [hxCoord, hyCoord] using hxy
  have hv : vx = vy := e.injective hxy'
  have hval : x - p0 = y - p0 := by
    simpa [vx, vy] using congrArg Subtype.val hv
  exact sub_left_injective hval

theorem HasAntipodalStrips.image_affineSpanCoord {d : ℕ} {points : Finset (Point d)}
    (hanti : HasAntipodalStrips points) {p0 : Point d}
    (hp0A : p0 ∈ affineSpan ℝ (points : Set (Point d))) :
    HasAntipodalStrips (points.image (affineSpanCoord points p0 hp0A)) := by
  intro a' ha' b' hb' hab' x' hx'
  rw [Finset.mem_image] at ha' hb' hx'
  rcases ha' with ⟨a, ha, rfl⟩
  rcases hb' with ⟨b, hb, rfl⟩
  rcases hx' with ⟨x, hx, rfl⟩
  have hab : a ≠ b := by
    intro h
    subst h
    exact hab' rfl
  have haA : a ∈ affineSpan ℝ (points : Set (Point d)) := subset_affineSpan ℝ _ ha
  have hbA : b ∈ affineSpan ℝ (points : Set (Point d)) := subset_affineSpan ℝ _ hb
  have hxA : x ∈ affineSpan ℝ (points : Set (Point d)) := subset_affineSpan ℝ _ hx
  constructor
  · simpa [affineSpanCoord_inner_eq hp0A haA hbA hxA] using
      (hanti a ha b hb hab x hx).1
  · simpa [affineSpanCoord_inner_eq hp0A hbA haA hxA] using
      (hanti a ha b hb hab x hx).2

theorem convexHull_volume_pos_of_affineSpan_eq_top {d : ℕ} (points : Finset (Point d))
    (hspan : affineSpan ℝ (points : Set (Point d)) = ⊤) :
    0 < MeasureTheory.volume (convexHull ℝ (points : Set (Point d))) := by
  have hnonempty : (interior (convexHull ℝ (points : Set (Point d)))).Nonempty := by
    exact interior_convexHull_nonempty_iff_affineSpan_eq_top.2 hspan
  exact (isOpen_interior.measure_pos MeasureTheory.volume hnonempty).trans_le
    (measure_mono interior_subset)

theorem affineSpan_ne_top_of_convexHull_volume_zero {d : ℕ} {points : Finset (Point d)}
    (hzero : MeasureTheory.volume (convexHull ℝ (points : Set (Point d))) = 0) :
    affineSpan ℝ (points : Set (Point d)) ≠ ⊤ := by
  intro hspan
  have hpos := convexHull_volume_pos_of_affineSpan_eq_top points hspan
  rw [hzero] at hpos
  exact (lt_irrefl (0 : ℝ≥0∞)) hpos











end

end ProofsInTheBook.Chapter15

open scoped ENNReal RealInnerProductSpace
open MeasureTheory
open ProofsInTheBook.Chapter15

theorem solution {d : ℕ} (points : Finset (Point d))
    (hanti : HasAntipodalStrips points) : points.card ≤ 2 ^ d := by
  classical
  revert points
  refine Nat.strong_induction_on d ?_
  intro d ih points hanti
  by_cases hvol0 : MeasureTheory.volume (convexHull ℝ (points : Set (Point d))) ≠ 0
  · exact antipodal_card_bound_of_positive_volume hanti hvol0
  · have hzero :
        MeasureTheory.volume (convexHull ℝ (points : Set (Point d))) = 0 := not_not.mp hvol0
    by_cases hempty : points = ∅
    · simp [hempty]
    · obtain ⟨p0, hp0⟩ := Finset.nonempty_iff_ne_empty.2 hempty
      have hp0A : p0 ∈ affineSpan ℝ (points : Set (Point d)) := subset_affineSpan ℝ _ hp0
      let k := Module.finrank ℝ (affineSpan ℝ (points : Set (Point d))).direction
      let f := affineSpanCoord points p0 hp0A
      let qpoints : Finset (Point k) := points.image f
      have hqanti : HasAntipodalStrips qpoints := by
        dsimp [qpoints, f]
        exact hanti.image_affineSpanCoord hp0A
      have hqcard : qpoints.card = points.card := by
        dsimp [qpoints, f]
        exact Finset.card_image_of_injOn (affineSpanCoord_injOn hp0A)
      have hspan_ne : affineSpan ℝ (points : Set (Point d)) ≠ ⊤ :=
        affineSpan_ne_top_of_convexHull_volume_zero hzero
      have hdir_ne : (affineSpan ℝ (points : Set (Point d))).direction ≠ ⊤ := by
        intro hdir
        exact hspan_ne ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨p0, hp0A⟩).1 hdir)
      have hklt : k < d := by
        dsimp [k]
        simpa [finrank_euclideanSpace_fin] using
          (Submodule.finrank_lt (K := ℝ) (V := Point d)
            (s := (affineSpan ℝ (points : Set (Point d))).direction) hdir_ne)
      have hqbound : qpoints.card ≤ 2 ^ k := ih k hklt qpoints hqanti
      calc
        points.card = qpoints.card := hqcard.symm
        _ ≤ 2 ^ k := hqbound
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_of_lt hklt)
