-- Prove2me | solution 1 for ProofsInTheBook.Chapter10.euclidean_sylvester_gallai
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-09-12T16:12:56.421143+00:00
-- url     : https://prove2.me/submissions/7c56f349-85ef-4c95-802b-49c54678c96f

import Mathlib
import Definitions.Def_ProofsInTheBook_Chapter10


/-!
# Chapter 10: Lines in the plane and decompositions of graphs

From "Proofs from THE BOOK":

**Sylvester-Gallai theorem**: Given a finite set of points in the plane,
not all collinear, there exists a line passing through exactly two of them.

The book's proof (by T. Gallai): Among all pairs (P, ℓ) where P is a point
not on line ℓ (spanned by other points), choose the pair minimizing
dist(P, ℓ). If ℓ contains ≥ 3 points, one can find a closer pair,
contradicting minimality.

The chapter also discusses graph decompositions and the related
theorem about bipartite graphs.
-/

namespace ProofsInTheBook.Chapter10

/-!
### Sylvester-Gallai theorem

The proof by Gallai's extremal argument is a beautiful application of
the well-ordering principle. The formalization requires:
1. A finite point set in ℝ² (or an affine plane)
2. The notion of a line through two points
3. The distance from a point to a line
4. The extremal argument

This geometric result is not yet in Mathlib.
-/












































/-! ## Concrete Euclidean Sylvester–Gallai (Kelly's proof — step 1)

The abstract development above reduces Sylvester–Gallai to the `gallai`
extremal step, supplied as a hypothesis.  To discharge that hypothesis we
work in the concrete plane `EuclideanSpace ℝ (Fin 2)` and follow L. M. Kelly's
metric proof: among all (point, spanned-line) pairs with the point off the
line, a pair of *minimum perpendicular distance* must determine an ordinary
line.

This section builds the metric foundation: the perpendicular distance to the
line through two points, its basic properties, and existence of a minimizing
pair over a finite non-collinear set. -/

section EuclideanSylvesterGallai

open Metric





/-- Perpendicular distance is nonnegative. -/
theorem perpDist_nonneg (P a b : EPoint) : 0 ≤ perpDist P a b :=
  Metric.infDist_nonneg







/-- The line through two points is a closed set (finite-dimensional affine
subspace), so a point with zero perpendicular distance actually lies on it. -/
theorem mem_of_perpDist_eq_zero {P a b : EPoint}
    (h : perpDist P a b = 0) : P ∈ affineSpan ℝ {a, b} := by
  have hclosed : IsClosed (affineSpan ℝ {a, b} : Set EPoint) :=
    (affineSpan ℝ {a, b}).closed_of_finiteDimensional
  have hne : (affineSpan ℝ {a, b} : Set EPoint).Nonempty :=
    ⟨a, left_mem_affineSpan_pair ℝ a b⟩
  rw [← SetLike.mem_coe, hclosed.mem_iff_infDist_zero hne]
  exact h



/-- A point off the line has strictly positive perpendicular distance. -/
theorem perpDist_pos {P a b : EPoint}
    (h : P ∉ affineSpan ℝ {a, b}) : 0 < perpDist P a b :=
  lt_of_le_of_ne (perpDist_nonneg P a b) fun hz => h (mem_of_perpDist_eq_zero hz.symm)









/-- The foot of the perpendicular lies on the line. -/
theorem foot_mem (P a b : EPoint) : foot P a b ∈ affineSpan ℝ {a, b} :=
  EuclideanGeometry.orthogonalProjection_mem P

/-- The perpendicular distance equals the distance to the foot of the
perpendicular (`orthogonalProjection` realises the infimum). -/
theorem perpDist_eq_dist_foot (P a b : EPoint) :
    perpDist P a b = dist P (foot P a b) :=
  (EuclideanGeometry.dist_orthogonalProjection_eq_infDist (affineSpan ℝ {a, b}) P).symm

/-- Pythagorean identity for the foot: `PR² = RF² + PF²` when `R` lies on the
line and `F` is the foot of the perpendicular from `P`. -/
theorem dist_sq_eq_foot {P a b R : EPoint} (hR : R ∈ affineSpan ℝ {a, b}) :
    dist R P * dist R P
      = dist R (foot P a b) * dist R (foot P a b)
        + dist P (foot P a b) * dist P (foot P a b) :=
  EuclideanGeometry.dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    (s := affineSpan ℝ {a, b}) P hR

/-- **Kelly step 3b: the closer point is strictly nearer on the cross-line.**
If `R` is on the line and `Q` lies between the foot `F` and `R`, while `P` is
off the line, then `dist Q R < dist P R`.  (Pythagoras: `PR² = RF² + PF²` with
`PF > 0`, and `QR ≤ FR` since `Q` is between `F` and `R`.) -/
theorem dist_lt_dist_of_wbtw_foot {P a b Q R : EPoint}
    (hP : P ∉ affineSpan ℝ {a, b}) (hR : R ∈ affineSpan ℝ {a, b})
    (hQ : Wbtw ℝ (foot P a b) Q R) : dist Q R < dist P R := by
  have hPF : 0 < dist P (foot P a b) := by
    rw [← perpDist_eq_dist_foot]; exact perpDist_pos hP
  -- `QR ≤ FR` from betweenness
  have hQR : dist Q R ≤ dist (foot P a b) R := by
    have hadd := hQ.dist_add_dist
    have hfq : 0 ≤ dist (foot P a b) Q := dist_nonneg
    -- dist F Q + dist Q R = dist F R
    rw [dist_comm Q R] at hadd ⊢
    nlinarith [hadd, hfq]
  -- Pythagoras, normalised to `dist P R` and `dist (foot) R`: PR² = FR² + PF²
  have hpyth : dist P R * dist P R
      = dist (foot P a b) R * dist (foot P a b) R
        + dist P (foot P a b) * dist P (foot P a b) := by
    have h := dist_sq_eq_foot (P := P) (a := a) (b := b) hR
    rwa [dist_comm R P, dist_comm R (foot P a b)] at h
  have hQRnn : 0 ≤ dist Q R := dist_nonneg
  have hFRnn : 0 ≤ dist (foot P a b) R := dist_nonneg
  -- squared inequality, then square-root monotonicity
  have hsq : dist Q R ^ 2 < dist P R ^ 2 := by
    rw [sq, sq]
    nlinarith [hpyth, mul_le_mul hQR hQR hQRnn hFRnn, mul_pos hPF hPF]
  exact lt_of_pow_lt_pow_left₀ 2 dist_nonneg hsq



open scoped RealInnerProductSpace in
/-- **Projection-length identity (Kelly step 3c core).**
The squared inner product `⟪P -ᵥ Y, Z -ᵥ Y⟫²` equals `(dist Y F)² · (dist Y Z)²`
where `F` is the foot of the perpendicular from `P` to line `YZ` — because the
component of `P -ᵥ Y` along the line direction is exactly `F -ᵥ Y`. -/
theorem inner_vsub_pair_sq (P Y Z : EPoint) :
    ⟪P -ᵥ Y, Z -ᵥ Y⟫ ^ 2 = dist Y (foot P Y Z) ^ 2 * dist Y Z ^ 2 := by
  set F := foot P Y Z with hF
  -- `F -ᵥ Y` lies in the line direction, so it is a multiple `t • (Z -ᵥ Y)`.
  have hFY : F -ᵥ Y ∈ vectorSpan ℝ ({Y, Z} : Set EPoint) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction (foot_mem P Y Z) (left_mem_affineSpan_pair ℝ Y Z)
  obtain ⟨t, ht⟩ := mem_vectorSpan_pair_rev.mp hFY   -- t • (Z -ᵥ Y) = F -ᵥ Y
  -- `P -ᵥ F` is orthogonal to the line direction.
  have hv : P -ᵥ F ∈ (vectorSpan ℝ ({Y, Z} : Set EPoint))ᗮ := by
    rw [← direction_affineSpan]
    exact EuclideanGeometry.vsub_orthogonalProjection_mem_direction_orthogonal
      (affineSpan ℝ {Y, Z}) P
  have hu : Z -ᵥ Y ∈ vectorSpan ℝ ({Y, Z} : Set EPoint) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction
      (right_mem_affineSpan_pair ℝ Y Z) (left_mem_affineSpan_pair ℝ Y Z)
  have horth : ⟪P -ᵥ F, Z -ᵥ Y⟫ = 0 :=
    real_inner_comm (Z -ᵥ Y) (P -ᵥ F) ▸ Submodule.inner_right_of_mem_orthogonal hu hv
  -- inner product collapses to `t · ‖Z -ᵥ Y‖²`
  have hinner : ⟪P -ᵥ Y, Z -ᵥ Y⟫ = t * ‖Z -ᵥ Y‖ ^ 2 := by
    have hdecomp : P -ᵥ Y = (P -ᵥ F) + (F -ᵥ Y) := (vsub_add_vsub_cancel P F Y).symm
    rw [hdecomp, inner_add_left, horth, zero_add, ← ht, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
  -- distances in terms of `‖Z -ᵥ Y‖`
  have hYZ : dist Y Z = ‖Z -ᵥ Y‖ := by
    rw [dist_eq_norm_vsub' EPoint Y Z]
  have hYF : dist Y F = |t| * ‖Z -ᵥ Y‖ := by
    rw [dist_eq_norm_vsub' EPoint Y F, ← ht, norm_smul, Real.norm_eq_abs]
  rw [hinner, hYZ, hYF]
  rw [mul_pow, mul_pow, sq_abs]
  ring

open scoped RealInnerProductSpace in
/-- **Gram / Lagrange identity for the perpendicular distance.**
`perpDist² · base² = ‖edge‖²·base² − ⟪edge, base⟫²` — i.e. doubled triangle
area squared, with apex `P` over base `YZ` (edge `P-ᵥY`). -/
theorem perpDist_sq_mul_dist_sq (P Y Z : EPoint) :
    perpDist P Y Z ^ 2 * dist Y Z ^ 2
      = dist P Y ^ 2 * dist Y Z ^ 2 - ⟪P -ᵥ Y, Z -ᵥ Y⟫ ^ 2 := by
  have hpyth := dist_sq_eq_foot (P := P) (a := Y) (b := Z) (left_mem_affineSpan_pair ℝ Y Z)
  have hkey := inner_vsub_pair_sq P Y Z
  have hfoot := perpDist_eq_dist_foot P Y Z
  rw [dist_comm Y P] at hpyth
  rw [hfoot]
  linear_combination hkey - dist Y Z ^ 2 * hpyth

open scoped RealInnerProductSpace in
/-- **Apex-invariance of the Gram quantity.**
The doubled-area-squared is independent of which vertex is the apex:
swapping apex `P`↔`Q` (bases `QR`↔`PR`) preserves the value.  Pure
inner-product algebra. -/
theorem gram_apex_symm (P Q R : EPoint) :
    dist P Q ^ 2 * dist Q R ^ 2 - ⟪P -ᵥ Q, R -ᵥ Q⟫ ^ 2
      = dist Q P ^ 2 * dist P R ^ 2 - ⟪Q -ᵥ P, R -ᵥ P⟫ ^ 2 := by
  have e1 : dist P Q ^ 2 = ⟪P -ᵥ Q, P -ᵥ Q⟫ := by
    rw [dist_eq_norm_vsub EPoint P Q, real_inner_self_eq_norm_sq]
  have e2 : dist Q R ^ 2 = ⟪R -ᵥ Q, R -ᵥ Q⟫ := by
    rw [dist_eq_norm_vsub' EPoint Q R, real_inner_self_eq_norm_sq]
  have e3 : dist Q P ^ 2 = ⟪P -ᵥ Q, P -ᵥ Q⟫ := by
    rw [dist_eq_norm_vsub' EPoint Q P, real_inner_self_eq_norm_sq]
  have e4 : dist P R ^ 2 = ⟪R -ᵥ P, R -ᵥ P⟫ := by
    rw [dist_eq_norm_vsub' EPoint P R, real_inner_self_eq_norm_sq]
  -- express the two cross-edge vectors via `a = P -ᵥ Q`, `b = R -ᵥ Q`
  have hQP : Q -ᵥ P = -(P -ᵥ Q) := (neg_vsub_eq_vsub_rev P Q).symm
  have hRP : R -ᵥ P = (R -ᵥ Q) - (P -ᵥ Q) := by
    rw [← vsub_sub_vsub_cancel_right R P Q]
  rw [e1, e2, e3, e4, hQP, hRP]
  simp only [inner_sub_left, inner_sub_right, inner_neg_left]
  rw [real_inner_comm (R -ᵥ Q) (P -ᵥ Q)]
  ring

open scoped RealInnerProductSpace in
/-- **Area identity (Kelly step 3c).**
`perpDist Q P R · dist P R = perpDist P Q R · dist Q R` — doubled triangle
area is base-independent.  Combines the Gram identity (both apexes) with
apex-invariance, then takes square roots. -/
theorem perpDist_mul_dist_eq (P Q R : EPoint) :
    perpDist Q P R * dist P R = perpDist P Q R * dist Q R := by
  have hsq : (perpDist Q P R * dist P R) ^ 2 = (perpDist P Q R * dist Q R) ^ 2 := by
    rw [mul_pow, mul_pow]
    rw [perpDist_sq_mul_dist_sq Q P R, perpDist_sq_mul_dist_sq P Q R]
    -- both equal the Gram quantity at the respective apex; apex-invariance links them
    have := gram_apex_symm P Q R
    nlinarith [this]
  have h1 : 0 ≤ perpDist Q P R * dist P R :=
    mul_nonneg (perpDist_nonneg _ _ _) dist_nonneg
  have h2 : 0 ≤ perpDist P Q R * dist Q R :=
    mul_nonneg (perpDist_nonneg _ _ _) dist_nonneg
  calc perpDist Q P R * dist P R
      = Real.sqrt ((perpDist Q P R * dist P R) ^ 2) := (Real.sqrt_sq h1).symm
    _ = Real.sqrt ((perpDist P Q R * dist Q R) ^ 2) := by rw [hsq]
    _ = perpDist P Q R * dist Q R := Real.sqrt_sq h2

/-- **Kelly's strict decrease (step 3d core).**
If `P` is off line `QR`, `Q ≠ R`, and `Q` lies between the foot of the
perpendicular from `P` and `R`, then the perpendicular distance from `Q` to
line `PR` is strictly smaller than that from `P` to line `QR`.  This is the
inequality that contradicts minimality in Kelly's proof. -/
theorem perpDist_lt_perpDist_of_wbtw {P Q R : EPoint}
    (hP : P ∉ affineSpan ℝ {Q, R}) (hw : Wbtw ℝ (foot P Q R) Q R) :
    perpDist Q P R < perpDist P Q R := by
  have hlt := dist_lt_dist_of_wbtw_foot hP (right_mem_affineSpan_pair ℝ Q R) hw
  have harea := perpDist_mul_dist_eq P Q R
  have hPR : 0 < dist P R :=
    dist_pos.mpr (fun h => hP (h ▸ right_mem_affineSpan_pair ℝ Q R))
  have hpos : 0 < perpDist P Q R := perpDist_pos hP
  nlinarith [harea, hlt, hPR, hpos, mul_lt_mul_of_pos_left hlt hpos]

/-- The carrier of the line through two points is a collinear set. -/
theorem collinear_coe_affineSpan_pair (a b : EPoint) :
    Collinear ℝ (↑(affineSpan ℝ ({a, b} : Set EPoint)) : Set EPoint) := by
  have hv : vectorSpan ℝ (↑(affineSpan ℝ ({a, b} : Set EPoint)) : Set EPoint)
      = vectorSpan ℝ ({a, b} : Set EPoint) := by
    rw [← direction_affineSpan, AffineSubspace.affineSpan_coe, direction_affineSpan]
  unfold Collinear
  rw [hv]
  exact collinear_pair ℝ a b

/-- Two distinct points on the line span the same line. -/
theorem affineSpan_pair_eq_of_mem {a b Q R : EPoint}
    (hQ : Q ∈ affineSpan ℝ ({a, b} : Set EPoint))
    (hR : R ∈ affineSpan ℝ ({a, b} : Set EPoint)) (hQR : Q ≠ R) :
    affineSpan ℝ ({Q, R} : Set EPoint) = affineSpan ℝ ({a, b} : Set EPoint) := by
  have h := (collinear_coe_affineSpan_pair a b).affineSpan_eq_of_ne
    (SetLike.mem_coe.mpr hQ) (SetLike.mem_coe.mpr hR) hQR
  rwa [AffineSubspace.affineSpan_coe] at h

/-- `perpDist` depends only on the line: equal spans give equal distances. -/
theorem perpDist_congr {P a b Q R : EPoint}
    (h : affineSpan ℝ ({Q, R} : Set EPoint) = affineSpan ℝ ({a, b} : Set EPoint)) :
    perpDist P Q R = perpDist P a b := by
  unfold perpDist
  rw [h]

/-- The foot of the perpendicular depends only on the line. -/
theorem foot_congr {P a b Q R : EPoint}
    (h : affineSpan ℝ ({Q, R} : Set EPoint) = affineSpan ℝ ({a, b} : Set EPoint)) :
    foot P Q R = foot P a b := by
  unfold foot
  exact EuclideanGeometry.orthogonalProjection_congr h rfl

/-- A point on the line is a scalar multiple of the direction `b -ᵥ a`, offset
from the foot of the perpendicular. -/
theorem exists_smul_vadd_foot {P a b X : EPoint} (hX : X ∈ affineSpan ℝ {a, b}) :
    ∃ r : ℝ, r • (b -ᵥ a) +ᵥ foot P a b = X := by
  have hmem : X -ᵥ foot P a b ∈ vectorSpan ℝ ({a, b} : Set EPoint) := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hX (foot_mem P a b)
  obtain ⟨r, hr⟩ := mem_vectorSpan_pair_rev.mp hmem
  exact ⟨r, by rw [hr, vsub_vadd]⟩

/-- **Pigeonhole (Kelly step 3d).** Among any three points on the line, two lie
on the same closed ray from the foot of the perpendicular — i.e. one is weakly
between the foot and the other. -/
theorem exists_wbtw_foot_of_three_mem {P a b x y z : EPoint}
    (hx : x ∈ affineSpan ℝ {a, b}) (hy : y ∈ affineSpan ℝ {a, b})
    (hz : z ∈ affineSpan ℝ {a, b}) :
    (Wbtw ℝ (foot P a b) x y ∨ Wbtw ℝ (foot P a b) y x) ∨
      (Wbtw ℝ (foot P a b) y z ∨ Wbtw ℝ (foot P a b) z y) ∨
      (Wbtw ℝ (foot P a b) x z ∨ Wbtw ℝ (foot P a b) z x) := by
  obtain ⟨rx, hrx⟩ := exists_smul_vadd_foot (P := P) hx
  obtain ⟨ry, hry⟩ := exists_smul_vadd_foot (P := P) hy
  obtain ⟨rz, hrz⟩ := exists_smul_vadd_foot (P := P) hz
  rcases le_total 0 rx with hx0 | hx0 <;> rcases le_total 0 ry with hy0 | hy0 <;>
    rcases le_total 0 rz with hz0 | hz0
  · exact Or.inl (hrx ▸ hry ▸ wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hx0 hy0)
  · exact Or.inl (hrx ▸ hry ▸ wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hx0 hy0)
  · exact Or.inr (Or.inr (hrx ▸ hrz ▸ wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hx0 hz0))
  · exact Or.inr (Or.inl (hry ▸ hrz ▸ wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hy0 hz0))
  · exact Or.inr (Or.inl (hry ▸ hrz ▸ wbtw_or_wbtw_smul_vadd_of_nonneg _ _ hy0 hz0))
  · exact Or.inr (Or.inr (hrx ▸ hrz ▸ wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hx0 hz0))
  · exact Or.inl (hrx ▸ hry ▸ wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hx0 hy0)
  · exact Or.inl (hrx ▸ hry ▸ wbtw_or_wbtw_smul_vadd_of_nonpos _ _ hx0 hy0)

/-- **Kelly step 2: a minimum-perpendicular-distance off-line pair exists.**
Over a finite point set with at least one off-line incidence, the perpendicular
distances of all off-line incidences attain a minimum — the well-ordering
(extremal) ingredient of Kelly's proof of Sylvester–Gallai.  Proved by
minimizing over `Finset.univ` of the finite incidence type (no `Finset.filter`
over the undecidable affine-membership predicate). -/
theorem exists_min_perpDist_offLine (S : Finset EPoint) (T : OffLineTriple S) :
    ∃ t : OffLineTriple S, ∀ t' : OffLineTriple S,
      perpDist t.P t.a t.b ≤ perpDist t'.P t'.a t'.b := by
  classical
  haveI : Fintype (OffLineTriple S) := Fintype.ofFinite _
  obtain ⟨t, _, hmin⟩ := Finset.univ.exists_min_image
    (fun t : OffLineTriple S => perpDist t.P t.a t.b) ⟨T, Finset.mem_univ T⟩
  exact ⟨t, fun t' => hmin t' (Finset.mem_univ t')⟩

open scoped Classical





end EuclideanSylvesterGallai

end ProofsInTheBook.Chapter10

open Metric
open scoped Classical
open ProofsInTheBook.Chapter10

theorem solution (S : Finset EPoint) (T : OffLineTriple S) :
    ∃ a b : EPoint, a ∈ S ∧ b ∈ S ∧ a ≠ b ∧
      (S.filter (· ∈ affineSpan ℝ ({a, b} : Set EPoint))).card = 2 := by
  classical
  obtain ⟨T₀, hmin⟩ := exists_min_perpDist_offLine S T
  refine ⟨T₀.a, T₀.b, T₀.ha, T₀.hb, T₀.hab, ?_⟩
  set pts := S.filter (· ∈ affineSpan ℝ ({T₀.a, T₀.b} : Set EPoint)) with hpts
  have haS : T₀.a ∈ pts :=
    Finset.mem_filter.mpr ⟨T₀.ha, left_mem_affineSpan_pair ℝ _ _⟩
  have hbS : T₀.b ∈ pts :=
    Finset.mem_filter.mpr ⟨T₀.hb, right_mem_affineSpan_pair ℝ _ _⟩
  -- the contradiction engine: no off-line incidence Q,R on the line can beat the minimum
  have contra : ∀ Q R, Q ∈ pts → R ∈ pts → Q ≠ R →
      Wbtw ℝ (foot T₀.P T₀.a T₀.b) Q R → False := by
    intro Q R hQ hR hQR hw
    have hQline : Q ∈ affineSpan ℝ {T₀.a, T₀.b} := (Finset.mem_filter.mp hQ).2
    have hRline : R ∈ affineSpan ℝ {T₀.a, T₀.b} := (Finset.mem_filter.mp hR).2
    have hspan : affineSpan ℝ ({Q, R} : Set EPoint) = affineSpan ℝ {T₀.a, T₀.b} :=
      affineSpan_pair_eq_of_mem hQline hRline hQR
    have hP_off : T₀.P ∉ affineSpan ℝ ({Q, R} : Set EPoint) := by rw [hspan]; exact T₀.hoff
    have hw' : Wbtw ℝ (foot T₀.P Q R) Q R := by rw [foot_congr hspan]; exact hw
    have hdec := perpDist_lt_perpDist_of_wbtw hP_off hw'
    rw [perpDist_congr hspan] at hdec
    -- (Q, T₀.P, R) is an off-line incidence
    have hPR : T₀.P ≠ R := fun h => T₀.hoff (h ▸ hRline)
    have hQ_off : Q ∉ affineSpan ℝ ({T₀.P, R} : Set EPoint) := by
      intro hQin
      have hRin : R ∈ affineSpan ℝ ({T₀.P, R} : Set EPoint) :=
        right_mem_affineSpan_pair ℝ _ _
      have he : affineSpan ℝ ({Q, R} : Set EPoint) = affineSpan ℝ {T₀.P, R} :=
        affineSpan_pair_eq_of_mem hQin hRin hQR
      rw [hspan] at he
      exact T₀.hoff (he ▸ left_mem_affineSpan_pair ℝ T₀.P R)
    let T' : OffLineTriple S :=
      ⟨Q, T₀.P, R, (Finset.mem_filter.mp hQ).1, T₀.hP, (Finset.mem_filter.mp hR).1, hPR, hQ_off⟩
    have := hmin T'
    -- this : perpDist T₀.P T₀.a T₀.b ≤ perpDist Q T₀.P R ;  hdec : perpDist Q T₀.P R < perpDist T₀.P T₀.a T₀.b
    exact absurd this (not_le.mpr hdec)
  -- card pts = 2: at least 2 (a,b), and a third point would contradict via pigeonhole
  have hge2 : 2 ≤ pts.card := by
    have hsub : ({T₀.a, T₀.b} : Finset EPoint) ⊆ pts := by
      intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact h ▸ haS
      · exact (Finset.mem_singleton.mp h) ▸ hbS
    calc 2 = ({T₀.a, T₀.b} : Finset EPoint).card := (Finset.card_pair T₀.hab).symm
      _ ≤ pts.card := Finset.card_le_card hsub
  rcases lt_or_eq_of_le hge2 with hlt | heq
  · exfalso
    have hlt2 : ({T₀.a, T₀.b} : Finset EPoint).card < pts.card := by
      rw [Finset.card_pair T₀.hab]; exact hlt
    obtain ⟨c, hc, hcab⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt2
    have hca : c ≠ T₀.a := fun h => hcab (h ▸ Finset.mem_insert_self _ _)
    have hcb : c ≠ T₀.b := fun h =>
      hcab (h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hcline : c ∈ affineSpan ℝ {T₀.a, T₀.b} := (Finset.mem_filter.mp hc).2
    rcases exists_wbtw_foot_of_three_mem (P := T₀.P)
      (left_mem_affineSpan_pair ℝ T₀.a T₀.b) (right_mem_affineSpan_pair ℝ T₀.a T₀.b) hcline with
      (h | h) | (h | h) | (h | h)
    · exact contra _ _ haS hbS T₀.hab h
    · exact contra _ _ hbS haS T₀.hab.symm h
    · exact contra _ _ hbS hc hcb.symm h
    · exact contra _ _ hc hbS hcb h
    · exact contra _ _ haS hc hca.symm h
    · exact contra _ _ hc haS hca h
  · exact heq.symm
