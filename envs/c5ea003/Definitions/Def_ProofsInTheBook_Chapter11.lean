-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter11
-- name    : ProofsInTheBook_Chapter11
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T15:58:46.659785+00:00
-- url     : https://prove2.me/theorems/5d4e42d8-1999-4a7b-886d-22848e6f4087
-- title:
--   Planar directions and finite projection-sweep structures
-- statement:
--   A planar point is a pair of real coordinates. A direction is either vertical or a real slope; a pair of distinct points determines its vertical direction when their first coordinates agree and otherwise the slope $(y_2-y_1)/(x_2-x_1)$. For a finite point set S, D(S) consists of all such directions. Noncollinearity means that three points of S have nonzero affine determinant. Directions have representative angles in $[0,\pi)$, and the oriented level at angle $\theta$ is
--   $$h_\theta(x,y)=-x\sin\theta+y\cos\theta.$$
--
--   The finite combinatorial structures record labelings of 2k distinct points, permutation states, contiguous position intervals and their reflections, and sequences beginning with the identity permutation and ending with the reversed permutation. A block move specifies disjoint intervals of length at least two and a permutation; a separate reversal condition requires reflection within each interval and fixed positions outside the intervals. The concrete sequence structures include this condition together with counts of labels crossing the division between the first and last k positions.
--
--   Projection-sweep structures associate steps with distinct planar directions and require each block to lie at one common level for its associated direction. Additional schedule and certificate structures record crossing counts, gaps between crossings, and the cyclic end-gap condition. Angle-indexed constructions and cyclic changes of starting angle provide the corresponding finite sweep data.
-- source:
--   Mathematical definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter11.lean#L26. Topic: Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 12, “The slope problem” (https://doi.org/10.1007/978-3-662-57265-8_12). The repository citation specifies the definitions retained here.

import Mathlib

/-!
# Chapter 11: The slope problem

From "Proofs from THE BOOK":

**The slope problem (Ungar's theorem)**: Given `n` points in the plane,
not all on a line, the number of distinct projective directions determined by
connecting pairs of points is at least `2 * ⌊n / 2⌋`.

The book's proof uses an elegant inductive argument combined with
a "rotating calipers" technique: consider the convex hull and analyze
how slopes change as we rotate a direction vector.

The Lean statement uses projective `Direction`s, so the vertical parallel class
is counted.  The fixed-axis finite slope set `slopesDeterminedBy` intentionally
omits vertical directions and is therefore only a corollary with a possible
loss of one.

This is closely related to the Sylvester-Gallai theorem (Chapter 10).
-/

namespace ProofsInTheBook.Chapter11

abbrev Point2 := ℝ × ℝ

inductive Direction where
  | vertical
  | finite (m : ℝ)

noncomputable instance : DecidableEq Direction :=
  Classical.decEq Direction

/-- The slope determined by an ordered pair of planar points. -/
noncomputable def slope (p q : Point2) : ℝ :=
  (q.2 - p.2) / (q.1 - p.1)

/-- The projective direction determined by a pair of points, including vertical lines. -/
noncomputable def direction (p q : Point2) : Direction :=
  if p.1 = q.1 then Direction.vertical else Direction.finite (slope p q)





/-- Coordinate of the line parallel to a projective direction through `p`. -/
noncomputable def directionLevel (d : Direction) (p : Point2) : ℝ :=
  match d with
  | Direction.vertical => p.1
  | Direction.finite m => p.2 - m * p.1

/-- Oriented projection level: the signed projection of point `p` onto the
line perpendicular to angle `θ`. Unlike `directionLevel`, this is continuous
in `θ` across the vertical direction. -/
noncomputable def orientedLevel (θ : ℝ) (p : Point2) : ℝ :=
  -p.1 * Real.sin θ + p.2 * Real.cos θ



theorem orientedLevel_add_pi (θ : ℝ) (p : Point2) :
    orientedLevel (θ + Real.pi) p = -orientedLevel θ p := by
  simp [orientedLevel, Real.sin_add, Real.cos_add, Real.sin_pi, Real.cos_pi]
  ring









theorem orientedLevel_sub_eq (θ : ℝ) (p q : Point2) :
    orientedLevel θ p - orientedLevel θ q =
      -(p.1 - q.1) * Real.sin θ + (p.2 - q.2) * Real.cos θ := by
  simp [orientedLevel]; ring

theorem orientedLevel_eq_cos_mul_directionLevel {θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (p : Point2) :
    orientedLevel θ p = Real.cos θ * directionLevel (Direction.finite (Real.tan θ)) p := by
  simp [orientedLevel, directionLevel, Real.tan_eq_sin_div_cos]
  field_simp; ring



noncomputable def Direction.angle : Direction → ℝ
  | .vertical => Real.pi / 2
  | .finite m => if 0 ≤ Real.arctan m then Real.arctan m else Real.arctan m + Real.pi

theorem Direction.angle_nonneg (d : Direction) : 0 ≤ d.angle := by
  cases d with
  | vertical => exact le_of_lt (div_pos Real.pi_pos two_pos)
  | finite m =>
    simp only [Direction.angle]
    split_ifs with h
    · exact h
    · linarith [Real.neg_pi_div_two_lt_arctan m]

theorem Direction.angle_lt_pi (d : Direction) : d.angle < Real.pi := by
  cases d with
  | vertical => show Real.pi / 2 < Real.pi; linarith [Real.pi_pos]
  | finite m =>
    simp only [Direction.angle]
    split_ifs with h
    · linarith [Real.arctan_lt_pi_div_two m]
    · linarith [Real.neg_pi_div_two_lt_arctan m]

theorem Direction.angle_injective : Function.Injective Direction.angle := by
  intro d1 d2 h
  match d1, d2 with
  | .vertical, .vertical => rfl
  | .vertical, .finite m =>
    simp only [Direction.angle] at h
    split_ifs at h with hm
    · linarith [Real.arctan_lt_pi_div_two m]
    · linarith [Real.neg_pi_div_two_lt_arctan m]
  | .finite m, .vertical =>
    simp only [Direction.angle] at h
    split_ifs at h with hm
    · linarith [Real.arctan_lt_pi_div_two m]
    · linarith [Real.neg_pi_div_two_lt_arctan m]
  | .finite m1, .finite m2 =>
    simp only [Direction.angle] at h
    split_ifs at h with h1 _h2 h1
    · exact congr_arg _ (Real.arctan_injective h)
    · linarith [Real.arctan_lt_pi_div_two m1, Real.neg_pi_div_two_lt_arctan m2]
    · linarith [Real.arctan_lt_pi_div_two m2, Real.neg_pi_div_two_lt_arctan m1]
    · exact congr_arg _ (Real.arctan_injective (by linarith))





/-- The finite set of all directions determined by distinct pairs of points. -/
noncomputable def directionsDeterminedBy (points : Finset Point2) : Finset Direction :=
  ((points.product points).filter fun pq => pq.1 ≠ pq.2).image
    (fun pq => direction pq.1 pq.2)

noncomputable def sortedDirectionAngles (points : Finset Point2) : List ℝ :=
  ((directionsDeterminedBy points).image Direction.angle).sort (· ≤ ·)

noncomputable def genericAngleBetween (θ₁ θ₂ : ℝ) : ℝ := (θ₁ + θ₂) / 2

theorem genericAngleBetween_lt {θ₁ θ₂ : ℝ} (h : θ₁ < θ₂) :
    θ₁ < genericAngleBetween θ₁ θ₂ := by
  simp [genericAngleBetween]; linarith

theorem genericAngleBetween_lt' {θ₁ θ₂ : ℝ} (h : θ₁ < θ₂) :
    genericAngleBetween θ₁ θ₂ < θ₂ := by
  simp [genericAngleBetween]; linarith

theorem genericAngleBetween_add_pi (θ₁ θ₂ : ℝ) :
    genericAngleBetween (θ₁ + Real.pi) (θ₂ + Real.pi) =
      genericAngleBetween θ₁ θ₂ + Real.pi := by
  unfold genericAngleBetween
  ring

/-- Three points are non-collinear, expressed by a nonzero determinant. -/
def NoncollinearTriple (p q r : Point2) : Prop :=
  ¬ (q.2 - p.2) * (r.1 - p.1) = (r.2 - p.2) * (q.1 - p.1)

/-- A finite point configuration is not contained in one line. -/
def NoncollinearSet (points : Finset Point2) : Prop :=
  ∃ p ∈ points, ∃ q ∈ points, ∃ r ∈ points, NoncollinearTriple p q r





structure PointLabeling (points : Finset Point2) (k : ℕ) where
  point : Fin (2 * k) → Point2
  mem_point : ∀ a, point a ∈ points
  point_injective : Function.Injective point
  point_surjective_on : ∀ p ∈ points, ∃ a, point a = p



namespace PointLabeling

noncomputable def ofCard {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k) : PointLabeling points k where
  point := fun a => (Finset.equivFinOfCardEq hcard).symm a
  mem_point := fun a => ((Finset.equivFinOfCardEq hcard).symm a).2
  point_injective := by
    intro a b h
    have hsub :
        (Finset.equivFinOfCardEq hcard).symm a =
          (Finset.equivFinOfCardEq hcard).symm b := by
      exact Subtype.ext h
    exact (Finset.equivFinOfCardEq hcard).symm.injective hsub
  point_surjective_on := by
    intro p hp
    refine ⟨(Finset.equivFinOfCardEq hcard) ⟨p, hp⟩, ?_⟩
    simp

end PointLabeling

namespace DirectionLabeling



end DirectionLabeling

/-! ### Sweep construction via oriented levels -/

noncomputable def sweepSort {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ : ℝ) : Equiv.Perm (Fin (2 * k)) :=
  Tuple.sort (fun a : Fin (2 * k) => orientedLevel θ (L.point a))

theorem sweepSort_monotone {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ : ℝ) :
    Monotone (fun i => orientedLevel θ (L.point (sweepSort L θ i))) := by
  have := Tuple.monotone_sort (fun a : Fin (2 * k) => orientedLevel θ (L.point a))
  exact this

noncomputable def PointLabeling.reindex {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (σ : Equiv.Perm (Fin (2 * k))) :
    PointLabeling points k where
  point := L.point ∘ σ
  mem_point := fun a => L.mem_point (σ a)
  point_injective := L.point_injective.comp σ.injective
  point_surjective_on := fun p hp => by
    rcases L.point_surjective_on p hp with ⟨a, ha⟩
    exact ⟨σ.symm a, by simp [Function.comp, ha]⟩

theorem sweepSort_reindex_eq_refl {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ₀ : ℝ) :
    sweepSort (L.reindex (sweepSort L θ₀)) θ₀ = Equiv.refl _ :=
  Tuple.sort_eq_refl_iff_monotone.mpr (sweepSort_monotone L θ₀)

theorem sort_neg_eq_revPerm {N : ℕ} {f : Fin N → ℝ}
    (hf : StrictMono f) :
    Tuple.sort (fun a => -f a) = Fin.revPerm := by
  symm
  rw [Tuple.eq_sort_iff]
  refine ⟨?_, ?_⟩
  · intro i j hij
    simp only [Function.comp, Fin.revPerm_apply]
    have : Fin.rev j ≤ Fin.rev i := Fin.rev_le_rev.mpr hij
    linarith [hf.monotone this]
  · intro i j hij heq
    exfalso
    simp only [Fin.revPerm_apply] at heq
    have h1 : f (Fin.rev i) = f (Fin.rev j) := by linarith
    exact absurd (Fin.rev_injective (hf.injective h1)) (ne_of_lt hij)

theorem sweepSort_strictMono_of_injective {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ : ℝ)
    (hinj : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ (L.point a))) :
    StrictMono (fun i => orientedLevel θ (L.point (sweepSort L θ i))) := by
  intro i j hij
  have hle := sweepSort_monotone L θ hij.le
  have hne : orientedLevel θ (L.point (sweepSort L θ i)) ≠
      orientedLevel θ (L.point (sweepSort L θ j)) :=
    fun h => absurd ((hinj.comp (sweepSort L θ).injective) h) (ne_of_lt hij)
  exact lt_of_le_of_ne hle hne

theorem sweepSort_reindex_add_pi_eq_revPerm {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ₀ : ℝ)
    (hinj : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₀ (L.point a))) :
    sweepSort (L.reindex (sweepSort L θ₀)) (θ₀ + Real.pi) = Fin.revPerm := by
  have key : (fun a => orientedLevel (θ₀ + Real.pi) (L.point ((sweepSort L θ₀) a))) =
      (fun a => -(orientedLevel θ₀ (L.point ((sweepSort L θ₀) a)))) := by
    ext a; exact orientedLevel_add_pi θ₀ (L.point ((sweepSort L θ₀) a))
  show Tuple.sort (fun a => orientedLevel (θ₀ + Real.pi)
    (L.point ((sweepSort L θ₀) a))) = Fin.revPerm
  rw [key]
  exact sort_neg_eq_revPerm (sweepSort_strictMono_of_injective L θ₀ hinj)

theorem sinusoid_at_most_one_zero_in_Ico_pi {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    {θ₁ θ₂ : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁' : θ₁ < Real.pi)
    (hθ₂ : 0 ≤ θ₂) (hθ₂' : θ₂ < Real.pi)
    (h1 : a * Real.sin θ₁ + b * Real.cos θ₁ = 0)
    (h2 : a * Real.sin θ₂ + b * Real.cos θ₂ = 0) :
    θ₁ = θ₂ := by
  by_contra hne
  have hsin : Real.sin (θ₁ - θ₂) = 0 := by
    have hsub : Real.sin θ₁ * Real.cos θ₂ - Real.sin θ₂ * Real.cos θ₁ =
        Real.sin (θ₁ - θ₂) := by rw [Real.sin_sub]; ring
    rcases hab with ha | hb
    · have h3 : a * (Real.sin θ₁ * Real.cos θ₂ - Real.sin θ₂ * Real.cos θ₁) = 0 := by
        linear_combination Real.cos θ₂ * h1 - Real.cos θ₁ * h2
      rw [hsub] at h3
      exact (mul_eq_zero.mp h3).resolve_left ha
    · have h3 : b * (Real.sin θ₁ * Real.cos θ₂ - Real.sin θ₂ * Real.cos θ₁) = 0 := by
        linear_combination -(Real.sin θ₂ * h1 - Real.sin θ₁ * h2)
      rw [hsub] at h3
      exact (mul_eq_zero.mp h3).resolve_left hb
  rw [Real.sin_eq_zero_iff] at hsin
  rcases hsin with ⟨n, hn⟩
  have hbound : |θ₁ - θ₂| < Real.pi := by
    rw [abs_lt]; constructor <;> linarith
  have : n = 0 := by
    by_contra hn0
    have h1le : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    have h1le_r : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast h1le
    have hpi_le : Real.pi ≤ |↑n * Real.pi| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      exact le_mul_of_one_le_left (le_of_lt Real.pi_pos) h1le_r
    linarith [show |↑n * Real.pi| = |θ₁ - θ₂| from by rw [hn]]
  have h0 : (0 : ℝ) = θ₁ - θ₂ := by rw [← hn]; simp [this]
  exact hne (by linarith)

theorem sinusoid_at_most_one_zero_of_abs_sub_lt_pi {a b : ℝ}
    (hab : a ≠ 0 ∨ b ≠ 0)
    {θ₁ θ₂ : ℝ} (hbound : |θ₁ - θ₂| < Real.pi)
    (h1 : a * Real.sin θ₁ + b * Real.cos θ₁ = 0)
    (h2 : a * Real.sin θ₂ + b * Real.cos θ₂ = 0) :
    θ₁ = θ₂ := by
  by_contra hne
  have hsin : Real.sin (θ₁ - θ₂) = 0 := by
    have hsub : Real.sin θ₁ * Real.cos θ₂ - Real.sin θ₂ * Real.cos θ₁ =
        Real.sin (θ₁ - θ₂) := by rw [Real.sin_sub]; ring
    rcases hab with ha | hb
    · have h3 : a * (Real.sin θ₁ * Real.cos θ₂ - Real.sin θ₂ * Real.cos θ₁) = 0 := by
        linear_combination Real.cos θ₂ * h1 - Real.cos θ₁ * h2
      rw [hsub] at h3
      exact (mul_eq_zero.mp h3).resolve_left ha
    · have h3 : b * (Real.sin θ₁ * Real.cos θ₂ - Real.sin θ₂ * Real.cos θ₁) = 0 := by
        linear_combination -(Real.sin θ₂ * h1 - Real.sin θ₁ * h2)
      rw [hsub] at h3
      exact (mul_eq_zero.mp h3).resolve_left hb
  rw [Real.sin_eq_zero_iff] at hsin
  rcases hsin with ⟨n, hn⟩
  have : n = 0 := by
    by_contra hn0
    have h1le : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
    have h1le_r : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast h1le
    have hpi_le : Real.pi ≤ |↑n * Real.pi| := by
      rw [abs_mul, abs_of_pos Real.pi_pos]
      exact le_mul_of_one_le_left (le_of_lt Real.pi_pos) h1le_r
    linarith [show |↑n * Real.pi| = |θ₁ - θ₂| from by rw [hn]]
  have h0 : (0 : ℝ) = θ₁ - θ₂ := by rw [← hn]; simp [this]
  exact hne (by linarith)

theorem orientedLevel_unique_tie_angle {p q : Point2} (hpq : p ≠ q)
    {θ₁ θ₂ : ℝ} (hθ₁ : 0 ≤ θ₁) (hθ₁' : θ₁ < Real.pi)
    (hθ₂ : 0 ≤ θ₂) (hθ₂' : θ₂ < Real.pi)
    (h1 : orientedLevel θ₁ p = orientedLevel θ₁ q)
    (h2 : orientedLevel θ₂ p = orientedLevel θ₂ q) :
    θ₁ = θ₂ := by
  have hab : -(p.1 - q.1) ≠ 0 ∨ (p.2 - q.2) ≠ 0 := by
    by_contra h; push Not at h
    exact hpq (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
  have heq1 : -(p.1 - q.1) * Real.sin θ₁ + (p.2 - q.2) * Real.cos θ₁ = 0 := by
    have := orientedLevel_sub_eq θ₁ p q; linarith
  have heq2 : -(p.1 - q.1) * Real.sin θ₂ + (p.2 - q.2) * Real.cos θ₂ = 0 := by
    have := orientedLevel_sub_eq θ₂ p q; linarith
  exact sinusoid_at_most_one_zero_in_Ico_pi hab hθ₁ hθ₁' hθ₂ hθ₂' heq1 heq2

theorem orientedLevel_unique_tie_angle_of_abs_sub_lt_pi {p q : Point2} (hpq : p ≠ q)
    {θ₁ θ₂ : ℝ} (hbound : |θ₁ - θ₂| < Real.pi)
    (h1 : orientedLevel θ₁ p = orientedLevel θ₁ q)
    (h2 : orientedLevel θ₂ p = orientedLevel θ₂ q) :
    θ₁ = θ₂ := by
  have hab : -(p.1 - q.1) ≠ 0 ∨ (p.2 - q.2) ≠ 0 := by
    by_contra h; push Not at h
    exact hpq (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
  have heq1 : -(p.1 - q.1) * Real.sin θ₁ + (p.2 - q.2) * Real.cos θ₁ = 0 := by
    have := orientedLevel_sub_eq θ₁ p q; linarith
  have heq2 : -(p.1 - q.1) * Real.sin θ₂ + (p.2 - q.2) * Real.cos θ₂ = 0 := by
    have := orientedLevel_sub_eq θ₂ p q; linarith
  exact sinusoid_at_most_one_zero_of_abs_sub_lt_pi hab hbound heq1 heq2



theorem monotone_contiguity {N : ℕ} {g : Fin N → ℝ}
    (hg : Monotone g) {a b c : Fin N} (hab : a ≤ b) (hbc : b ≤ c)
    (hac : g a = g c) : g a = g b := by
  linarith [hg hab, hg hbc]

theorem neg_of_neg_of_continuousOn_of_no_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hfa : f a < 0) (hno_zero : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    f b < 0 := by
  by_contra hge
  push Not at hge
  have hfb_pos : 0 < f b :=
    lt_of_le_of_ne hge (Ne.symm (hno_zero b (Set.right_mem_Icc.mpr hab)))
  exact hno_zero _ (intermediate_value_Icc hab hcont
    (⟨le_of_lt hfa, le_of_lt hfb_pos⟩ : (0 : ℝ) ∈ Set.Icc (f a) (f b))).choose_spec.1
    (intermediate_value_Icc hab hcont
    (⟨le_of_lt hfa, le_of_lt hfb_pos⟩ : (0 : ℝ) ∈ Set.Icc (f a) (f b))).choose_spec.2

theorem orientedLevel_diff_continuous (p q : Point2) :
    Continuous (fun θ => orientedLevel θ p - orientedLevel θ q) := by
  simp only [orientedLevel]; fun_prop

theorem neg_at_start_of_neg_at_end {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hfb : f b < 0) (hno_zero : ∀ x ∈ Set.Icc a b, f x ≠ 0) :
    f a < 0 := by
  by_contra hge
  push Not at hge
  have hfa_pos : 0 < f a :=
    lt_of_le_of_ne hge (Ne.symm (hno_zero a (Set.left_mem_Icc.mpr hab)))
  exact hno_zero _ (intermediate_value_Icc' hab hcont
    (⟨le_of_lt hfb, le_of_lt hfa_pos⟩ : (0 : ℝ) ∈ Set.Icc (f b) (f a))).choose_spec.1
    (intermediate_value_Icc' hab hcont
    (⟨le_of_lt hfb, le_of_lt hfa_pos⟩ : (0 : ℝ) ∈ Set.Icc (f b) (f a))).choose_spec.2

theorem orientedLevel_order_preserved {p q : Point2}
    {θ₁ θ₂ : ℝ} (h12 : θ₁ ≤ θ₂)
    (hlt : orientedLevel θ₁ p < orientedLevel θ₁ q)
    (hno_tie : ∀ θ ∈ Set.Icc θ₁ θ₂,
      orientedLevel θ p ≠ orientedLevel θ q) :
    orientedLevel θ₂ p < orientedLevel θ₂ q := by
  have hcont := (orientedLevel_diff_continuous p q).continuousOn (s := Set.Icc θ₁ θ₂)
  linarith [neg_of_neg_of_continuousOn_of_no_zero h12 hcont (by linarith : (fun θ =>
    orientedLevel θ p - orientedLevel θ q) θ₁ < 0)
    (fun x hx h => hno_tie x hx (by linarith))]

theorem orientedLevel_order_preserved_backward {p q : Point2}
    {θ₁ θ₂ : ℝ} (h12 : θ₁ ≤ θ₂)
    (hlt : orientedLevel θ₂ p < orientedLevel θ₂ q)
    (hno_tie : ∀ θ ∈ Set.Icc θ₁ θ₂,
      orientedLevel θ p ≠ orientedLevel θ q) :
    orientedLevel θ₁ p < orientedLevel θ₁ q := by
  have hcont := (orientedLevel_diff_continuous p q).continuousOn (s := Set.Icc θ₁ θ₂)
  linarith [neg_at_start_of_neg_at_end h12 hcont (by linarith : (fun θ =>
    orientedLevel θ p - orientedLevel θ q) θ₂ < 0)
    (fun x hx h => hno_tie x hx (by linarith))]

theorem sinusoid_product_formula {a b : ℝ}
    {θ₁ θ₀ θ₂ : ℝ}
    (hzero : a * Real.sin θ₀ + b * Real.cos θ₀ = 0) :
    (a * Real.sin θ₁ + b * Real.cos θ₁) * (a * Real.sin θ₂ + b * Real.cos θ₂) =
      (a ^ 2 + b ^ 2) * Real.sin (θ₁ - θ₀) * Real.sin (θ₂ - θ₀) := by
  have h1 : (a * Real.sin θ₁ + b * Real.cos θ₁) * Real.cos θ₀ =
      a * Real.sin (θ₁ - θ₀) := by
    rw [Real.sin_sub]; linear_combination Real.cos θ₁ * hzero
  have h2 : (a * Real.sin θ₂ + b * Real.cos θ₂) * Real.cos θ₀ =
      a * Real.sin (θ₂ - θ₀) := by
    rw [Real.sin_sub]; linear_combination Real.cos θ₂ * hzero
  have h3 : (a * Real.sin θ₁ + b * Real.cos θ₁) * Real.sin θ₀ =
      -(b * Real.sin (θ₁ - θ₀)) := by
    rw [Real.sin_sub]; linear_combination Real.sin θ₁ * hzero
  have h4 : (a * Real.sin θ₂ + b * Real.cos θ₂) * Real.sin θ₀ =
      -(b * Real.sin (θ₂ - θ₀)) := by
    rw [Real.sin_sub]; linear_combination Real.sin θ₂ * hzero
  set d₁ := a * Real.sin θ₁ + b * Real.cos θ₁
  set d₂ := a * Real.sin θ₂ + b * Real.cos θ₂
  set s₁ := Real.sin (θ₁ - θ₀)
  set s₂ := Real.sin (θ₂ - θ₀)
  have h12 : d₁ * d₂ * Real.cos θ₀ ^ 2 = a ^ 2 * s₁ * s₂ := by
    calc d₁ * d₂ * Real.cos θ₀ ^ 2
        = (d₁ * Real.cos θ₀) * (d₂ * Real.cos θ₀) := by ring
      _ = (a * s₁) * (a * s₂) := by rw [h1, h2]
      _ = a ^ 2 * s₁ * s₂ := by ring
  have h34 : d₁ * d₂ * Real.sin θ₀ ^ 2 = b ^ 2 * s₁ * s₂ := by
    calc d₁ * d₂ * Real.sin θ₀ ^ 2
        = (d₁ * Real.sin θ₀) * (d₂ * Real.sin θ₀) := by ring
      _ = (-(b * s₁)) * (-(b * s₂)) := by rw [h3, h4]
      _ = b ^ 2 * s₁ * s₂ := by ring
  calc d₁ * d₂
      = d₁ * d₂ * 1 := by ring
    _ = d₁ * d₂ * (Real.sin θ₀ ^ 2 + Real.cos θ₀ ^ 2) := by
        rw [Real.sin_sq_add_cos_sq]
    _ = d₁ * d₂ * Real.sin θ₀ ^ 2 + d₁ * d₂ * Real.cos θ₀ ^ 2 := by ring
    _ = b ^ 2 * s₁ * s₂ + a ^ 2 * s₁ * s₂ := by linarith
    _ = (a ^ 2 + b ^ 2) * s₁ * s₂ := by ring

theorem sinusoid_sign_change_at_zero {a b : ℝ} (hab : a ≠ 0 ∨ b ≠ 0)
    {θ₁ θ₀ θ₂ : ℝ}
    (h10 : θ₁ < θ₀) (h02 : θ₀ < θ₂) (h_span : θ₂ - θ₁ < Real.pi)
    (hzero : a * Real.sin θ₀ + b * Real.cos θ₀ = 0)
    (hneg : a * Real.sin θ₁ + b * Real.cos θ₁ < 0) :
    0 < a * Real.sin θ₂ + b * Real.cos θ₂ := by
  have hab2 : 0 < a ^ 2 + b ^ 2 := by
    rcases hab with ha | hb
    · positivity
    · positivity
  have hsin1 : Real.sin (θ₁ - θ₀) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  have hsin2 : 0 < Real.sin (θ₂ - θ₀) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hprod := sinusoid_product_formula hzero (θ₁ := θ₁) (θ₂ := θ₂)
  by_contra hge
  push Not at hge
  have hprod_neg : (a ^ 2 + b ^ 2) * Real.sin (θ₁ - θ₀) * Real.sin (θ₂ - θ₀) < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hab2 hsin1) hsin2
  linarith [mul_nonneg (le_of_lt (neg_pos.mpr hneg)) (neg_nonneg.mpr hge),
            show -(a * Real.sin θ₁ + b * Real.cos θ₁) *
              -(a * Real.sin θ₂ + b * Real.cos θ₂) =
              (a * Real.sin θ₁ + b * Real.cos θ₁) *
              (a * Real.sin θ₂ + b * Real.cos θ₂) from by ring]

theorem orientedLevel_order_reversed_at_event {p q : Point2} (hpq : p ≠ q)
    {θ₁ θ_e θ₂ : ℝ} (h1e : θ₁ < θ_e) (he2 : θ_e < θ₂)
    (h_span : θ₂ - θ₁ < Real.pi)
    (hlt : orientedLevel θ₁ p < orientedLevel θ₁ q)
    (htie : orientedLevel θ_e p = orientedLevel θ_e q)
    (_hne2 : orientedLevel θ₂ p ≠ orientedLevel θ₂ q) :
    orientedLevel θ₂ q < orientedLevel θ₂ p := by
  have hab : -(p.1 - q.1) ≠ 0 ∨ (p.2 - q.2) ≠ 0 := by
    by_contra h; push Not at h
    exact hpq (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
  have heq_e : -(p.1 - q.1) * Real.sin θ_e + (p.2 - q.2) * Real.cos θ_e = 0 := by
    have := orientedLevel_sub_eq θ_e p q; linarith
  have hneg : -(p.1 - q.1) * Real.sin θ₁ + (p.2 - q.2) * Real.cos θ₁ < 0 := by
    have := orientedLevel_sub_eq θ₁ p q; linarith
  have hpos := sinusoid_sign_change_at_zero hab h1e he2 h_span heq_e hneg
  have hsub := orientedLevel_sub_eq θ₂ p q
  linarith



theorem sweepSort_eq_of_strictMono {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {θ : ℝ}
    (σ : Equiv.Perm (Fin (2 * k)))
    (hstrict : StrictMono (fun i => orientedLevel θ (L.point (σ i)))) :
    sweepSort L θ = σ := by
  show Tuple.sort (fun a => orientedLevel θ (L.point a)) = σ
  symm; rw [Tuple.eq_sort_iff]
  exact ⟨hstrict.monotone, fun i j hij heq =>
    absurd heq (ne_of_lt (hstrict hij))⟩

theorem sweepSort_reindex_of_injective {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (τ : Equiv.Perm (Fin (2 * k))) {θ : ℝ}
    (hinj : Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel θ (L.point a))) :
    sweepSort (L.reindex τ) θ = (sweepSort L θ).trans τ.symm := by
  apply sweepSort_eq_of_strictMono
  intro i j hij
  have hstrict := sweepSort_strictMono_of_injective L θ hinj hij
  simpa [PointLabeling.reindex, Function.comp, Equiv.trans_apply] using hstrict

theorem sweepSort_add_pi_eq_revPerm_trans {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ₀ : ℝ)
    (hinj : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₀ (L.point a))) :
    sweepSort L (θ₀ + Real.pi) = Fin.revPerm.trans (sweepSort L θ₀) := by
  have hinj_add :
      Function.Injective (fun a : Fin (2 * k) => orientedLevel (θ₀ + Real.pi) (L.point a)) := by
    intro a b hab
    apply hinj
    have ha := orientedLevel_add_pi θ₀ (L.point a)
    have hb := orientedLevel_add_pi θ₀ (L.point b)
    linarith
  have hrev := sweepSort_reindex_add_pi_eq_revPerm L θ₀ hinj
  have hreindex :=
    sweepSort_reindex_of_injective L (sweepSort L θ₀) hinj_add
  rw [hreindex] at hrev
  apply Equiv.ext
  intro a
  have happ := congrFun (congrArg DFunLike.coe hrev) a
  have happ' := congrArg (sweepSort L θ₀) happ
  simpa [Equiv.trans_apply] using happ'

/-! ### Level-block extraction from monotone functions -/

noncomputable def levelBlockLo {N : ℕ} (f : Fin N → ℝ) (i : Fin N) : Fin N :=
  (Finset.univ.filter (fun j : Fin N => f j = f i ∧ j ≤ i)).min'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, le_refl _⟩⟩

noncomputable def levelBlockHi {N : ℕ} (f : Fin N → ℝ) (i : Fin N) : Fin N :=
  (Finset.univ.filter (fun j : Fin N => f j = f i ∧ i ≤ j)).max'
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, le_refl _⟩⟩

 theorem levelBlockLo_mem {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    f (levelBlockLo f i) = f i ∧ levelBlockLo f i ≤ i := by
  have h := Finset.min'_mem (Finset.univ.filter (fun j : Fin N => f j = f i ∧ j ≤ i))
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, le_refl _⟩⟩
  exact (Finset.mem_filter.mp h).2

theorem levelBlockLo_le {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    levelBlockLo f i ≤ i := levelBlockLo_mem.2

theorem levelBlockLo_val {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    f (levelBlockLo f i) = f i := levelBlockLo_mem.1

 theorem levelBlockHi_mem {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    f (levelBlockHi f i) = f i ∧ i ≤ levelBlockHi f i := by
  have h := Finset.max'_mem (Finset.univ.filter (fun j : Fin N => f j = f i ∧ i ≤ j))
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, le_refl _⟩⟩
  exact (Finset.mem_filter.mp h).2

theorem levelBlockHi_ge {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    i ≤ levelBlockHi f i := levelBlockHi_mem.2

theorem levelBlockHi_val {N : ℕ} {f : Fin N → ℝ} {i : Fin N} :
    f (levelBlockHi f i) = f i := levelBlockHi_mem.1

theorem monotone_levelBlock_eq {N : ℕ} {f : Fin N → ℝ} (hf : Monotone f)
    {i j : Fin N} (hij : levelBlockLo f i ≤ j) (hji : j ≤ levelBlockHi f i) :
    f j = f i := by
  linarith [monotone_contiguity hf hij hji
    (levelBlockLo_val (i := i) |>.trans (levelBlockHi_val (i := i) |>.symm)),
    levelBlockLo_val (f := f) (i := i)]

noncomputable def levelBlockMirror {N : ℕ} (f : Fin N → ℝ) (p : Fin N) : Fin N :=
  ⟨(levelBlockLo f p).val + (levelBlockHi f p).val - p.val, by
    have hlo := levelBlockLo_le (f := f) (i := p)
    have hhi := levelBlockHi_ge (f := f) (i := p)
    omega⟩

theorem levelBlockMirror_mem_block {N : ℕ} {f : Fin N → ℝ} (p : Fin N) :
    (levelBlockLo f p).val ≤ (levelBlockMirror f p).val ∧
      (levelBlockMirror f p).val ≤ (levelBlockHi f p).val := by
  simp [levelBlockMirror]
  have hlo := levelBlockLo_le (f := f) (i := p)
  have hhi := levelBlockHi_ge (f := f) (i := p)
  exact ⟨by omega, by omega⟩

theorem levelBlockMirror_val {N : ℕ} {f : Fin N → ℝ} (hf : Monotone f) (p : Fin N) :
    f (levelBlockMirror f p) = f p := by
  apply monotone_levelBlock_eq hf
  · exact Fin.le_def.mpr (levelBlockMirror_mem_block p).1
  · exact Fin.le_def.mpr (levelBlockMirror_mem_block p).2

theorem sweepSort_event_level_monotone {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {θ₁ θ_e : ℝ}
    (hinj : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₁ (L.point a)))
    (h1e : θ₁ ≤ θ_e)
    (hno_tie_before : ∀ a b : Fin (2 * k), a ≠ b →
      ∀ θ ∈ Set.Ioo θ₁ θ_e, orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b)) :
    Monotone (fun i => orientedLevel θ_e (L.point (sweepSort L θ₁ i))) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_refl _
  · have hstrict := sweepSort_strictMono_of_injective L θ₁ hinj hlt
    by_cases heq : orientedLevel θ_e (L.point (sweepSort L θ₁ i)) =
        orientedLevel θ_e (L.point (sweepSort L θ₁ j))
    · exact le_of_eq heq
    · apply le_of_lt
      apply orientedLevel_order_preserved h1e hstrict
      intro θ hθ
      rcases eq_or_lt_of_le hθ.1 with rfl | h_lt₁
      · exact fun h => absurd h (ne_of_lt hstrict)
      · rcases eq_or_lt_of_le hθ.2 with rfl | h_lt_e
        · exact heq
        · exact hno_tie_before _ _ (fun h =>
            ne_of_lt hlt ((sweepSort L θ₁).injective h)) θ ⟨h_lt₁, h_lt_e⟩

theorem levelBlockMirror_reverses_within_block {N : ℕ} {f : Fin N → ℝ}
    (_hf : Monotone f) {i j : Fin N} (hij : i < j) (hfij : f i = f j) :
    levelBlockMirror f j < levelBlockMirror f i := by
  simp [levelBlockMirror]
  have hlo_i := levelBlockLo_le (f := f) (i := i)
  have hhi_i := levelBlockHi_ge (f := f) (i := i)
  have hlo_j := levelBlockLo_le (f := f) (i := j)
  have hhi_j := levelBlockHi_ge (f := f) (i := j)
  have h_i_in_j_lo : i ∈ Finset.univ.filter (fun k : Fin N => f k = f j ∧ k ≤ j) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfij, le_of_lt hij⟩
  have h_j_in_i_hi : j ∈ Finset.univ.filter (fun k : Fin N => f k = f i ∧ i ≤ k) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfij.symm, le_of_lt hij⟩
  have hlo_j_le_i : levelBlockLo f j ≤ i :=
    Finset.min'_le _ _ h_i_in_j_lo
  have hlo_eq : levelBlockLo f i = levelBlockLo f j := by
    apply le_antisymm
    · apply Finset.min'_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (levelBlockLo_val (i := j)).trans hfij.symm, hlo_j_le_i⟩
    · apply Finset.min'_le
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (levelBlockLo_val (i := i)).trans hfij,
        (levelBlockLo_le (i := i)).trans (le_of_lt hij)⟩
  have hhi_i_ge_j : j ≤ levelBlockHi f i :=
    Finset.le_max' _ _ h_j_in_i_hi
  have hhi_eq : levelBlockHi f i = levelBlockHi f j := by
    apply le_antisymm
    · apply Finset.le_max'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (levelBlockHi_val (i := i)).trans hfij,
        hhi_i_ge_j⟩
    · apply Finset.le_max'
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (levelBlockHi_val (i := j)).trans hfij.symm,
        (le_of_lt hij).trans (levelBlockHi_ge (i := j))⟩
  omega

theorem levelBlockMirror_preserves_across_blocks {N : ℕ} {f : Fin N → ℝ}
    (hf : Monotone f) {i j : Fin N} (_hij : i < j) (hfij : f i < f j) :
    levelBlockMirror f i < levelBlockMirror f j := by
  have hlo_i := levelBlockLo_le (f := f) (i := i)
  have hhi_i := levelBlockHi_ge (f := f) (i := i)
  have hlo_j := levelBlockLo_le (f := f) (i := j)
  have hhi_j := levelBlockHi_ge (f := f) (i := j)
  have hhi_lt_lo : levelBlockHi f i < levelBlockLo f j := by
    by_contra h
    push Not at h
    linarith [hf h, levelBlockLo_val (f := f) (i := j),
              levelBlockHi_val (f := f) (i := i)]
  simp only [levelBlockMirror, Fin.lt_def]
  omega

theorem levelBlockLo_of_mem_block {N : ℕ} {f : Fin N → ℝ}
    {i j : Fin N} (hfij : f j = f i)
    (hlo : (levelBlockLo f i).val ≤ j.val) :
    levelBlockLo f j = levelBlockLo f i := by
  have h1 : levelBlockLo f j ≤ levelBlockLo f i :=
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (levelBlockLo_val (i := i)).trans hfij.symm, Fin.le_def.mpr hlo⟩)
  have h2 : levelBlockLo f i ≤ levelBlockLo f j :=
    Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (levelBlockLo_val (i := j)).trans hfij,
      h1.trans levelBlockLo_le⟩)
  exact le_antisymm h1 h2

theorem levelBlockHi_of_mem_block {N : ℕ} {f : Fin N → ℝ}
    {i j : Fin N} (hfij : f j = f i)
    (hhi : j.val ≤ (levelBlockHi f i).val) :
    levelBlockHi f j = levelBlockHi f i := by
  have h1 : levelBlockHi f i ≤ levelBlockHi f j :=
    Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (levelBlockHi_val (i := i)).trans hfij.symm, Fin.le_def.mpr hhi⟩)
  have h2 : levelBlockHi f j ≤ levelBlockHi f i :=
    Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (levelBlockHi_val (i := j)).trans hfij,
      levelBlockHi_ge.trans h1⟩)
  exact le_antisymm h2 h1

theorem levelBlockMirror_involutive {N : ℕ} {f : Fin N → ℝ} (hf : Monotone f)
    (p : Fin N) : levelBlockMirror f (levelBlockMirror f p) = p := by
  have hmem := levelBlockMirror_mem_block (f := f) p
  have hval := levelBlockMirror_val hf p
  have hlo_eq := levelBlockLo_of_mem_block hval hmem.1
  have hhi_eq := levelBlockHi_of_mem_block hval hmem.2
  have hlo_v := congrArg Fin.val hlo_eq
  have hhi_v := congrArg Fin.val hhi_eq
  apply Fin.ext
  show (levelBlockLo f (levelBlockMirror f p)).val +
    (levelBlockHi f (levelBlockMirror f p)).val -
    (levelBlockMirror f p).val = p.val
  rw [hlo_v, hhi_v]; simp [levelBlockMirror]
  have := (Fin.le_def.mp (levelBlockLo_le (f := f) (i := p)))
  have := (Fin.le_def.mp (levelBlockHi_ge (f := f) (i := p)))
  omega

noncomputable def levelBlockMirrorPerm {N : ℕ} (f : Fin N → ℝ) (hf : Monotone f) :
    Equiv.Perm (Fin N) where
  toFun := levelBlockMirror f
  invFun := levelBlockMirror f
  left_inv := levelBlockMirror_involutive hf
  right_inv := levelBlockMirror_involutive hf

theorem sweepSort_event_compose {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    {θ₁ θ_e θ₂ : ℝ}
    (hinj₁ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₁ (L.point a)))
    (hinj₂ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₂ (L.point a)))
    (h1e : θ₁ < θ_e) (he2 : θ_e < θ₂) (h_span : θ₂ - θ₁ < Real.pi)
    (honly_event : ∀ a b : Fin (2 * k), L.point a ≠ L.point b →
      ∀ θ ∈ Set.Icc θ₁ θ₂, θ ≠ θ_e →
        orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b))
    (hg_mono : Monotone (fun i => orientedLevel θ_e (L.point (sweepSort L θ₁ i)))) :
    sweepSort L θ₂ =
      (levelBlockMirrorPerm (fun i => orientedLevel θ_e (L.point (sweepSort L θ₁ i))) hg_mono).trans
        (sweepSort L θ₁) := by
  set σ₁ := sweepSort L θ₁
  set g : Fin (2 * k) → ℝ := fun i => orientedLevel θ_e (L.point (σ₁ i))
  apply sweepSort_eq_of_strictMono
  intro i j hij
  show orientedLevel θ₂ (L.point (σ₁ (levelBlockMirror g i))) <
    orientedLevel θ₂ (L.point (σ₁ (levelBlockMirror g j)))
  by_cases hcase : g i = g j
  · -- Same block: mirror reverses, then event reverses back
    have hm := levelBlockMirror_reverses_within_block hg_mono hij hcase
    have hord := sweepSort_strictMono_of_injective L θ₁ hinj₁ hm
    have hne : L.point (σ₁ (levelBlockMirror g j)) ≠ L.point (σ₁ (levelBlockMirror g i)) :=
      fun h => ne_of_lt hord (congr_arg (orientedLevel θ₁) h)
    have htie : orientedLevel θ_e (L.point (σ₁ (levelBlockMirror g j))) =
        orientedLevel θ_e (L.point (σ₁ (levelBlockMirror g i))) := by
      show g (levelBlockMirror g j) = g (levelBlockMirror g i)
      simp only [levelBlockMirror_val hg_mono, hcase]
    have hne₂ : orientedLevel θ₂ (L.point (σ₁ (levelBlockMirror g j))) ≠
        orientedLevel θ₂ (L.point (σ₁ (levelBlockMirror g i))) :=
      fun h => ne_of_lt hm (σ₁.injective (hinj₂ h))
    exact orientedLevel_order_reversed_at_event hne h1e he2 h_span hord htie hne₂
  · -- Different blocks: mirror preserves, event preserves
    have hlt : g i < g j := lt_of_le_of_ne (hg_mono hij.le) hcase
    have hm := levelBlockMirror_preserves_across_blocks hg_mono hij hlt
    have hord := sweepSort_strictMono_of_injective L θ₁ hinj₁ hm
    have hne : L.point (σ₁ (levelBlockMirror g i)) ≠ L.point (σ₁ (levelBlockMirror g j)) :=
      fun h => ne_of_lt hord (congr_arg (orientedLevel θ₁) h)
    apply orientedLevel_order_preserved (le_of_lt (lt_trans h1e he2)) hord
    intro θ hθ
    rcases eq_or_ne θ θ_e with rfl | hne_θ
    · exact fun h => ne_of_lt hlt (by
        have h1 := levelBlockMirror_val hg_mono (f := g) (p := i)
        have h2 := levelBlockMirror_val hg_mono (f := g) (p := j)
        change g (levelBlockMirror g i) = g (levelBlockMirror g j) at h
        linarith)
    · exact honly_event _ _ hne θ hθ hne_θ

theorem label_index_lt_of_orientedLevel_lt {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ₀ : ℝ)
    (hid : sweepSort L θ₀ = Equiv.refl _)
    {a b : Fin (2 * k)}
    (h : orientedLevel θ₀ (L.point a) < orientedLevel θ₀ (L.point b)) :
    a.val < b.val := by
  by_contra hge
  push Not at hge
  linarith [(show Monotone (fun a => orientedLevel θ₀ (L.point a)) from
    Tuple.sort_eq_refl_iff_monotone.mp hid) (Fin.le_def.mpr hge)]







theorem left_ne_right_of_noncollinear {p q r : Point2}
    (h : NoncollinearTriple p q r) : p ≠ q := by
  intro hpq
  subst q
  exact h (by ring)

theorem left_ne_third_of_noncollinear {p q r : Point2}
    (h : NoncollinearTriple p q r) : p ≠ r := by
  intro hpr
  subst r
  exact h (by ring)

theorem determinant_eq_zero_of_same_direction_from_left {p q r : Point2}
    (hdir : direction p q = direction p r) :
    (q.2 - p.2) * (r.1 - p.1) = (r.2 - p.2) * (q.1 - p.1) := by
  classical
  by_cases hxq : p.1 = q.1
  · by_cases hxr : p.1 = r.1
    · have hqzero : q.1 - p.1 = 0 := by rw [← hxq, sub_self]
      have hrzero : r.1 - p.1 = 0 := by rw [← hxr, sub_self]
      rw [hqzero, hrzero, mul_zero, mul_zero]
    · simp [direction, hxq] at hdir
      exact False.elim (hxr (hxq.trans hdir))
  · by_cases hxr : p.1 = r.1
    · simp [direction, hxr] at hdir
      exact False.elim (hxq (hxr.trans hdir))
    · have hslope : slope p q = slope p r := by
        simpa [direction, hxq, hxr] using hdir
      have hqden : q.1 - p.1 ≠ 0 := by
        exact sub_ne_zero.mpr (Ne.symm hxq)
      have hrden : r.1 - p.1 ≠ 0 := by
        exact sub_ne_zero.mpr (Ne.symm hxr)
      unfold slope at hslope
      field_simp [hqden, hrden] at hslope
      linarith

theorem directionLevel_eq_of_direction_eq {p q : Point2} {d : Direction}
    (hdir : direction p q = d) :
    directionLevel d p = directionLevel d q := by
  cases d with
  | vertical =>
      by_cases hx : p.1 = q.1
      · simp [directionLevel, hx]
      · simp [direction, hx] at hdir
  | finite m =>
      by_cases hx : p.1 = q.1
      · simp [direction, hx] at hdir
      · have hslope : slope p q = m := by
          simpa [direction, hx] using hdir
        have hden : q.1 - p.1 ≠ 0 := by
          exact sub_ne_zero.mpr (Ne.symm hx)
        unfold slope at hslope
        field_simp [hden] at hslope
        simp [directionLevel]
        linarith

theorem direction_eq_of_directionLevel_eq {p q : Point2} {d : Direction}
    (hpq : p ≠ q) (hlevel : directionLevel d p = directionLevel d q) :
    direction p q = d := by
  cases d with
  | vertical =>
      simp [directionLevel] at hlevel
      simp [direction, hlevel]
  | finite m =>
      simp [directionLevel] at hlevel
      by_cases hx : p.1 = q.1
      · have hy : p.2 = q.2 := by
          rw [hx] at hlevel
          linarith
        exact False.elim (hpq (Prod.ext hx hy))
      · have hden : q.1 - p.1 ≠ 0 := by
          exact sub_ne_zero.mpr (Ne.symm hx)
        simp [direction, hx, slope]
        field_simp [hden]
        linarith





theorem direction_mem_directionsDeterminedBy {points : Finset Point2} {p q : Point2}
    (hp : p ∈ points) (hq : q ∈ points) (hpq : p ≠ q) :
    direction p q ∈ directionsDeterminedBy points := by
  exact Finset.mem_image.mpr ⟨(p, q), by simp [hp, hq, hpq], rfl⟩

theorem mem_directionsDeterminedBy_iff_exists_equal_level {points : Finset Point2}
    {d : Direction} :
    d ∈ directionsDeterminedBy points ↔
      ∃ p ∈ points, ∃ q ∈ points, p ≠ q ∧
        directionLevel d p = directionLevel d q := by
  constructor
  · intro hd
    rcases Finset.mem_image.mp hd with ⟨pq, hpq_mem, hpq_dir⟩
    rcases pq with ⟨p, q⟩
    rcases Finset.mem_filter.mp hpq_mem with ⟨hpq_prod, hpq_ne⟩
    rcases Finset.mem_product.mp hpq_prod with ⟨hp, hq⟩
    exact ⟨p, hp, q, hq, hpq_ne, directionLevel_eq_of_direction_eq hpq_dir⟩
  · rintro ⟨p, hp, q, hq, hpq_ne, hlevel⟩
    have hdir : direction p q = d :=
      direction_eq_of_directionLevel_eq hpq_ne hlevel
    rw [← hdir]
    exact direction_mem_directionsDeterminedBy hp hq hpq_ne

theorem PointLabeling.direction_mem {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {a b : Fin (2 * k)}
    (hab : a ≠ b) :
    direction (L.point a) (L.point b) ∈ directionsDeterminedBy points := by
  exact direction_mem_directionsDeterminedBy (L.mem_point a) (L.mem_point b)
    (fun hp => hab (L.point_injective hp))







namespace DirectionLabeling







end DirectionLabeling

theorem directions_from_noncollinear_triple_ne {p q r : Point2}
    (hnon : NoncollinearTriple p q r) :
    direction p q ≠ direction p r := by
  intro hdir
  exact hnon (determinant_eq_zero_of_same_direction_from_left hdir)













































/--
The numerical core of Ungar's even-cardinality proof.  The crossing moves have
orders `d_i`; every letter crosses the central barrier at least once, giving
`n ≤ Σ 2 d_i`, while the T/O/C block argument fits disjoint blocks of total
length `Σ 2 d_i` inside one period of length `t`.
-/
structure UngarCountingCertificate (n t : ℕ) where
  crossingCount : ℕ
  order : Fin crossingCount → ℕ
  letters_cross : n ≤ ∑ i : Fin crossingCount, 2 * order i
  blocks_fit : (∑ i : Fin crossingCount, 2 * order i) ≤ t



/-- Integer telescoping identity for Ungar's adjacent crossing-order sums. -/
theorem ungar_adjacent_order_sum_identity_int (c : ℕ) (hc : 2 ≤ c) (d : ℕ → ℤ) :
    (d 0 + d (c - 1) - 1)
        + ∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)
      =
    2 * (∑ i ∈ Finset.range c, d i) - c := by
  induction c with
  | zero => omega
  | succ c ih =>
      by_cases hc2 : 2 ≤ c
      · have ihc := ih hc2
        rw [Finset.sum_range_succ]
        rw [show c + 1 - 1 = c by omega]
        have hsum_adj :
            (∑ i ∈ Finset.range c, (d i + d (i + 1) - 1)) =
              (∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)) +
                (d (c - 1) + d c - 1) := by
          rw [← show c - 1 + 1 = c by omega]
          rw [Finset.sum_range_succ]
          simp [Nat.sub_add_cancel (by omega : 1 ≤ c)]
        rw [hsum_adj]
        have hrewrite :
            (d 0 + d c - 1) +
                ((∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)) +
                  (d (c - 1) + d c - 1))
              =
            ((d 0 + d (c - 1) - 1) +
                ∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1))
              + 2 * d c - 1 := by ring
        rw [hrewrite, ihc]
        rw [show ((c + 1 : ℕ) : ℤ) = (c : ℤ) + 1 by norm_num]
        ring_nf
      · have hc_eq : c = 1 := by omega
        subst c
        simp [Finset.sum_range_succ]
        ring

/-- Telescoping identity for adjacent index gaps. -/
theorem ungar_adjacent_gap_sum_identity_int (c : ℕ) (hc : 1 ≤ c) (a : ℕ → ℤ) :
    (∑ i ∈ Finset.range (c - 1), (a (i + 1) - a i - 1))
      = a (c - 1) - a 0 - (c - 1 : ℤ) := by
  induction c with
  | zero => omega
  | succ c ih =>
      by_cases hc1 : 1 ≤ c
      · have ihc := ih hc1
        rw [show c + 1 - 1 = c by omega]
        have hsum :
            (∑ i ∈ Finset.range c, (a (i + 1) - a i - 1)) =
              (∑ i ∈ Finset.range (c - 1), (a (i + 1) - a i - 1)) +
                (a c - a (c - 1) - 1) := by
          rw [← show c - 1 + 1 = c by omega]
          rw [Finset.sum_range_succ]
          simp [Nat.sub_add_cancel hc1]
        rw [hsum, ihc]
        rw [show ((c + 1 : ℕ) : ℤ) = (c : ℤ) + 1 by norm_num]
        ring
      · have hc_eq : c = 0 := by omega
        subst c
        simp

/--
Finite schedule of crossing moves in Ungar's middle-barrier proof.  The
`idx` and gap fields are the data coming from the T/O/C pattern; the
`blocks_fit` part of the downstream counting certificate is proved from
these gap assumptions by `UngarMoveSchedule.sum_orders_le_moves`.
-/
structure UngarMoveSchedule (k r : ℕ) where
  crossingCount : ℕ
  order : Fin crossingCount → ℕ
  letters_cross : 2 * k ≤ ∑ i : Fin crossingCount, 2 * order i
  two_le_crossingCount : 2 ≤ crossingCount
  idx : Fin crossingCount → Fin r
  idx_strict : ∀ {i j : Fin crossingCount}, i < j → (idx i).val < (idx j).val
  order_pos : ∀ i, 0 < order i
  gap_between :
    ∀ (i : ℕ) (hi : i + 1 < crossingCount),
      order ⟨i, by omega⟩ + order ⟨i + 1, by omega⟩ - 1 ≤
        (idx ⟨i + 1, by omega⟩).val - (idx ⟨i, by omega⟩).val - 1
  gap_ends :
    order ⟨0, by omega⟩ + order ⟨crossingCount - 1, by omega⟩ - 1 ≤
      (idx ⟨0, by omega⟩).val +
        (r - 1 - (idx ⟨crossingCount - 1, by omega⟩).val)







theorem UngarMoveSchedule.sum_orders_le_moves_from_gaps_int {k r : ℕ}
    (C : UngarMoveSchedule k r) :
    (2 * (∑ i : Fin C.crossingCount, (C.order i : ℤ)) : ℤ) ≤ r := by
  classical
  let c := C.crossingCount
  let d : ℕ → ℤ := fun i =>
    if h : i < c then (C.order ⟨i, h⟩ : ℤ) else 0
  let a : ℕ → ℤ := fun i =>
    if h : i < c then ((C.idx ⟨i, h⟩).val : ℤ) else 0
  have horder_sum :
      (∑ i ∈ Finset.range c, d i) =
        ∑ i : Fin c, (C.order i : ℤ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _hi
    simp [d]
  have hbetween :
      (∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)) ≤
        ∑ i ∈ Finset.range (c - 1), (a (i + 1) - a i - 1) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have hi0 : i < c := by omega
    have hi1 : i + 1 < c := by omega
    have hg := C.gap_between i (by omega)
    have hpos0 : 0 < C.order ⟨i, hi0⟩ := C.order_pos ⟨i, hi0⟩
    have hpos1 : 0 < C.order ⟨i + 1, hi1⟩ := C.order_pos ⟨i + 1, hi1⟩
    simp [d, a, hi0, hi1]
    omega
  have hgap_sum :
      (∑ i ∈ Finset.range (c - 1), (a (i + 1) - a i - 1)) =
        a (c - 1) - a 0 - (c - 1 : ℤ) := by
    have hc1 : 1 ≤ c := le_trans (by norm_num : 1 ≤ 2) C.two_le_crossingCount
    exact ungar_adjacent_gap_sum_identity_int c hc1 a
  have hbetween' :
      (∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)) ≤
        a (c - 1) - a 0 - (c - 1 : ℤ) := by
    exact le_trans hbetween (le_of_eq hgap_sum)
  have hends :
      d 0 + d (c - 1) - 1 ≤ a 0 + ((r : ℤ) - 1 - a (c - 1)) := by
    have h0 : 0 < c := lt_of_lt_of_le (by norm_num : 0 < 2) C.two_le_crossingCount
    have hlast : c - 1 < c := Nat.sub_lt h0 (by norm_num)
    have hg := C.gap_ends
    have hpos0 : 0 < C.order ⟨0, h0⟩ := C.order_pos ⟨0, h0⟩
    have hpos_last : 0 < C.order ⟨c - 1, hlast⟩ := C.order_pos ⟨c - 1, hlast⟩
    have hlast_eq :
        (⟨c - 1, hlast⟩ : Fin C.crossingCount) =
          ⟨C.crossingCount - 1, by
            have hcpos : 0 < C.crossingCount :=
              lt_of_lt_of_le (by norm_num : 0 < 2) C.two_le_crossingCount
            exact Nat.sub_lt hcpos (by norm_num)⟩ := by
      apply Fin.ext
      simp [c]
    rw [← hlast_eq] at hg
    simp [d, a, h0, hlast]
    omega
  have hleft_le :
      (d 0 + d (c - 1) - 1) +
          ∑ i ∈ Finset.range (c - 1), (d i + d (i + 1) - 1)
        ≤
      (a 0 + ((r : ℤ) - 1 - a (c - 1))) +
          (a (c - 1) - a 0 - (c - 1 : ℤ)) := by
    exact add_le_add hends hbetween'
  have hidentity :=
    ungar_adjacent_order_sum_identity_int c C.two_le_crossingCount d
  rw [hidentity] at hleft_le
  rw [horder_sum] at hleft_le
  have hright_eq :
      (a 0 + ((r : ℤ) - 1 - a (c - 1))) +
          (a (c - 1) - a 0 - (c - 1 : ℤ)) =
        (r : ℤ) - c := by
    have hc_cast : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by
      have hc1 : 1 ≤ c := le_trans (by norm_num : 1 ≤ 2) C.two_le_crossingCount
      omega
    ring
  rw [hright_eq] at hleft_le
  linarith

theorem UngarMoveSchedule.sum_orders_le_moves_from_gaps {k r : ℕ}
    (C : UngarMoveSchedule k r) :
    (∑ i : Fin C.crossingCount, 2 * C.order i) ≤ r := by
  have hint := C.sum_orders_le_moves_from_gaps_int
  have hsum :
      ((∑ i : Fin C.crossingCount, 2 * C.order i : ℕ) : ℤ) =
        2 * (∑ i : Fin C.crossingCount, (C.order i : ℤ)) := by
    simp [Finset.mul_sum]
  have hcast : ((∑ i : Fin C.crossingCount, 2 * C.order i : ℕ) : ℤ) ≤ (r : ℤ) := by
    rw [hsum]
    exact hint
  exact_mod_cast hcast

theorem UngarMoveSchedule.sum_orders_le_moves {k r : ℕ}
    (C : UngarMoveSchedule k r) :
    (∑ i : Fin C.crossingCount, 2 * C.order i) ≤ r :=
  C.sum_orders_le_moves_from_gaps

def UngarMoveSchedule.toCountingCertificate {k r : ℕ}
    (C : UngarMoveSchedule k r) : UngarCountingCertificate (2 * k) r where
  crossingCount := C.crossingCount
  order := C.order
  letters_cross := C.letters_cross
  blocks_fit := C.sum_orders_le_moves







































/-! ### Finite allowable-sequence vocabulary -/

/-- A permutation state maps position to label. -/
abbrev State (N : ℕ) := Equiv.Perm (Fin N)

/-- The left side of the middle barrier in `2 * k` positions. -/
def middleLeft (k : ℕ) (p : Fin (2 * k)) : Prop :=
  p.val < k

/-- A label crosses the middle barrier between two permutation states. -/
def crossesMiddle (k : ℕ) (π ρ : State (2 * k)) (a : Fin (2 * k)) : Prop :=
  middleLeft k (π.symm a) ↔ ¬ middleLeft k (ρ.symm a)

/-- The source index of step `j` in a sequence of `r + 1` states. -/
def stepFrom {r : ℕ} (j : Fin r) : Fin (r + 1) :=
  ⟨j.val, lt_trans j.isLt (Nat.lt_succ_self r)⟩

/-- The target index of step `j` in a sequence of `r + 1` states. -/
def stepTo {r : ℕ} (j : Fin r) : Fin (r + 1) :=
  ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩

/-- The reverse permutation on `Fin N`. -/
def reverseFin (N : ℕ) : State N :=
  Fin.revPerm

theorem middleLeft_reverseFin_symm_iff_not {k : ℕ} (a : Fin (2 * k)) :
    middleLeft k ((reverseFin (2 * k)).symm a) ↔ ¬ middleLeft k a := by
  simp [reverseFin, middleLeft, Fin.revPerm_symm]
  omega

theorem crossesMiddle_relabel {k : ℕ}
    (π ρ τ : State (2 * k)) (a : Fin (2 * k)) :
    crossesMiddle k (π.trans τ.symm) (ρ.trans τ.symm) a ↔
      crossesMiddle k π ρ (τ a) := by
  simp [crossesMiddle]

theorem crossesMiddle_reverse_left {k : ℕ}
    (π ρ : State (2 * k)) (a : Fin (2 * k)) :
    crossesMiddle k ((reverseFin (2 * k)).trans π) ((reverseFin (2 * k)).trans ρ) a ↔
      crossesMiddle k π ρ a := by
  unfold crossesMiddle
  simp
  rw [middleLeft_reverseFin_symm_iff_not (k := k) (π.symm a),
    middleLeft_reverseFin_symm_iff_not (k := k) (ρ.symm a)]
  tauto

/--
A finite generalized allowable sequence, reduced to the data needed for the
middle-barrier counting layer: a list of permutation states beginning at the
identity and ending at the reverse permutation.
-/
structure GeneralizedAllowableSequence (k r : ℕ) where
  π : Fin (r + 1) → State (2 * k)
  start : π ⟨0, Nat.succ_pos r⟩ = Equiv.refl (Fin (2 * k))
  finish : π ⟨r, Nat.lt_succ_self r⟩ = reverseFin (2 * k)

namespace GeneralizedAllowableSequence

/-- If a Boolean value changes between the endpoints of a finite sequence,
then it changes across some adjacent step. -/
theorem every_label_crosses {k r : ℕ} (A : GeneralizedAllowableSequence k r)
    (a : Fin (2 * k)) :
    ∃ j : Fin r,
      crossesMiddle k (A.π (stepFrom j)) (A.π (stepTo j)) a := by
  classical
  by_contra hnone
  push Not at hnone
  have hsame_step :
      ∀ j : Fin r,
        middleLeft k ((A.π (stepFrom j)).symm a) ↔
          middleLeft k ((A.π (stepTo j)).symm a) := by
    intro j
    have hnot := hnone j
    unfold crossesMiddle at hnot
    by_cases hfrom : middleLeft k ((A.π (stepFrom j)).symm a) <;>
      by_cases hto : middleLeft k ((A.π (stepTo j)).symm a) <;>
      simp [hfrom, hto] at hnot ⊢
  let b (i : ℕ) (hi : i ≤ r) : Prop :=
    middleLeft k ((A.π ⟨i, Nat.lt_succ_of_le hi⟩).symm a)
  have hsame_to_start :
      ∀ i : ℕ, ∀ hi : i ≤ r, b i hi ↔ b 0 (Nat.zero_le r) := by
    intro i
    induction i with
    | zero =>
        intro hi
        rfl
    | succ i ih =>
        intro hi
        have hi_prev : i ≤ r := Nat.le_of_succ_le hi
        have hi_lt : i < r := Nat.lt_of_succ_le hi
        have hstep := hsame_step ⟨i, hi_lt⟩
        have hprev := ih hi_prev
        change b i hi_prev ↔ b (i + 1) hi at hstep
        exact hstep.symm.trans hprev
  have hend_same :
      middleLeft k ((A.π ⟨r, Nat.lt_succ_self r⟩).symm a) ↔
        middleLeft k ((A.π ⟨0, Nat.succ_pos r⟩).symm a) := by
    simpa [b] using hsame_to_start r (le_rfl : r ≤ r)
  have hstart :
      middleLeft k ((A.π ⟨0, Nat.succ_pos r⟩).symm a) ↔ middleLeft k a := by
    rw [A.start]
    simp
  have hend :
      middleLeft k ((A.π ⟨r, Nat.lt_succ_self r⟩).symm a) ↔
        ¬ middleLeft k a := by
    rw [A.finish]
    exact middleLeft_reverseFin_symm_iff_not a
  have hbad :
      middleLeft k ((A.π ⟨0, Nat.succ_pos r⟩).symm a) ↔
        ¬ middleLeft k ((A.π ⟨0, Nat.succ_pos r⟩).symm a) := by
    exact hend_same.symm.trans (hend.trans (not_congr hstart.symm))
  by_cases h0 : middleLeft k ((A.π ⟨0, Nat.succ_pos r⟩).symm a)
  · exact (hbad.mp h0) h0
  · exact h0 (hbad.mpr h0)

/-- The number of labels crossing the middle barrier in one step. -/
noncomputable def crossingLabelsCard {k r : ℕ} (A : GeneralizedAllowableSequence k r)
    (j : Fin r) : ℕ := by
  classical
  exact Fintype.card
    {a : Fin (2 * k) //
      crossesMiddle k (A.π (stepFrom j)) (A.π (stepTo j)) a}



/--
Step-level crossing counts for a generalized allowable sequence.  The
geometric block-reversal layer will prove `crossed_labels_card`; this finite
layer only uses the count.
-/
structure StepCounting {k r : ℕ} (A : GeneralizedAllowableSequence k r) where
  order : Fin r → ℕ
  crossed_labels_card :
    ∀ j : Fin r, crossingLabelsCard A j = 2 * order j

/--
Every label crosses the middle at least once, so the sum of step crossing
counts is at least the number of labels.
-/
theorem StepCounting.letters_cross {k r : ℕ} {A : GeneralizedAllowableSequence k r}
    (C : StepCounting A) :
    2 * k ≤ ∑ j : Fin r, 2 * C.order j := by
  classical
  let pick : Fin (2 * k) → Fin r := fun a =>
    Classical.choose (A.every_label_crosses a)
  let packed :
      Fin (2 * k) →
        Σ j : Fin r,
          {a : Fin (2 * k) //
            crossesMiddle k (A.π (stepFrom j)) (A.π (stepTo j)) a} :=
    fun a => ⟨pick a, ⟨a, Classical.choose_spec (A.every_label_crosses a)⟩⟩
  let unpack :
      (Σ j : Fin r,
        {a : Fin (2 * k) //
          crossesMiddle k (A.π (stepFrom j)) (A.π (stepTo j)) a}) →
        Fin (2 * k) :=
    fun x => x.2.1
  have hinj : Function.Injective packed := by
    intro a b h
    have hval := congrArg unpack h
    simpa [packed, unpack] using hval
  have hcard := Fintype.card_le_of_injective packed hinj
  have hcard' :
      2 * k ≤
        ∑ j : Fin r, crossingLabelsCard A j := by
    simpa [crossingLabelsCard, Fintype.card_fin, Fintype.card_sigma] using hcard
  have hsum :
      (∑ j : Fin r, crossingLabelsCard A j) =
        ∑ j : Fin r, 2 * C.order j := by
    apply Finset.sum_congr rfl
    intro j _hj
    exact C.crossed_labels_card j
  rwa [hsum] at hcard'





end GeneralizedAllowableSequence

/-! ### Sweep → GeneralizedAllowableSequence bridge -/

theorem reverseFin_eq_revPerm (N : ℕ) : reverseFin N = Fin.revPerm := rfl

theorem sweepSort_reindex_refl {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ : ℝ) :
    sweepSort (L.reindex (Equiv.refl _)) θ = sweepSort L θ := rfl

theorem sweepSort_add_pi_eq_reverseFin {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) (θ₀ : ℝ)
    (hstart : sweepSort L θ₀ = Equiv.refl _)
    (hinj : Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel θ₀ (L.point a))) :
    sweepSort L (θ₀ + Real.pi) = reverseFin (2 * k) := by
  rw [reverseFin_eq_revPerm]
  have h := sweepSort_reindex_add_pi_eq_revPerm L θ₀ hinj
  rwa [hstart, sweepSort_reindex_refl] at h

noncomputable def GeneralizedAllowableSequence.ofSweepAngles
    {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    (θ : Fin ((directionsDeterminedBy points).card + 1) → ℝ)
    (hstart : sweepSort L (θ ⟨0, Nat.succ_pos _⟩) = Equiv.refl _)
    (hfinish_eq : θ ⟨(directionsDeterminedBy points).card, Nat.lt_succ_self _⟩ =
      θ ⟨0, Nat.succ_pos _⟩ + Real.pi)
    (hinj : Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel (θ ⟨0, Nat.succ_pos _⟩) (L.point a))) :
    GeneralizedAllowableSequence k (directionsDeterminedBy points).card where
  π := fun j => sweepSort L (θ j)
  start := hstart
  finish := by
    rw [hfinish_eq]
    exact sweepSort_add_pi_eq_reverseFin L _ hstart hinj

/-! ### Consecutive block moves -/

/-- A consecutive interval of positions in `Fin N`. -/
structure PositionInterval (N : ℕ) where
  lo : ℕ
  hi : ℕ
  lo_le_hi : lo ≤ hi
  hi_lt : hi < N

namespace PositionInterval

/-- Membership of a position in a consecutive interval. -/
def Mem {N : ℕ} (I : PositionInterval N) (p : Fin N) : Prop :=
  I.lo ≤ p.val ∧ p.val ≤ I.hi

/-- The set of positions in a consecutive interval. -/
def toSet {N : ℕ} (I : PositionInterval N) : Set (Fin N) :=
  {p | I.Mem p}

/-- The finite set of positions in a consecutive interval. -/
noncomputable def toFinset {N : ℕ} (I : PositionInterval N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter I.Mem

theorem mem_toFinset {N : ℕ} {I : PositionInterval N} {p : Fin N} :
    p ∈ I.toFinset ↔ I.Mem p := by
  simp [toFinset]

/-- Mirror a position across the midpoint of a consecutive interval. -/
def mirror {N : ℕ} (I : PositionInterval N) (p : Fin N) (hp : I.Mem p) : Fin N :=
  ⟨I.lo + I.hi - p.val, by
    rcases hp with ⟨hlo, hhi⟩
    have hle_hi : I.lo + I.hi - p.val ≤ I.hi := by omega
    exact lt_of_le_of_lt hle_hi I.hi_lt⟩

theorem mirror_mem {N : ℕ} (I : PositionInterval N) (p : Fin N) (hp : I.Mem p) :
    I.Mem (I.mirror p hp) := by
  rcases hp with ⟨hlo, hhi⟩
  constructor
  · dsimp [mirror]
    omega
  · dsimp [mirror]
    omega







theorem le_mirror_iff_le_sub {N k : ℕ} (I : PositionInterval N)
    (p : Fin N) (hp : I.Mem p) (hk : k ≤ I.hi) :
    k ≤ (I.mirror p hp).val ↔ p.val ≤ I.lo + I.hi - k := by
  rcases hp with ⟨hlo, hhi⟩
  dsimp [mirror]
  omega

theorem mirror_lt_iff_sub_lt {N k : ℕ} (I : PositionInterval N)
    (p : Fin N) (hp : I.Mem p) :
    (I.mirror p hp).val < k ↔ I.lo + I.hi - p.val < k := by
  rfl

/-- The number of positions in a consecutive interval. -/
def length {N : ℕ} (I : PositionInterval N) : ℕ :=
  I.hi + 1 - I.lo







/--
For `2 * k` positions, the order of an interval crossing the middle barrier.
The barrier is between positions `k - 1` and `k`.
-/
def crossOrder (k : ℕ) (I : PositionInterval (2 * k)) : ℕ :=
  if I.lo < k ∧ k ≤ I.hi then
    Nat.min (k - I.lo) (I.hi + 1 - k)
  else
    0

theorem crossOrder_eq_zero_of_not_crossing {k : ℕ} {I : PositionInterval (2 * k)}
    (h : ¬ (I.lo < k ∧ k ≤ I.hi)) :
    I.crossOrder k = 0 := by
  simp [crossOrder, h]

theorem crossOrder_eq_min_of_crossing {k : ℕ} {I : PositionInterval (2 * k)}
    (h : I.lo < k ∧ k ≤ I.hi) :
    I.crossOrder k = Nat.min (k - I.lo) (I.hi + 1 - k) := by
  simp [crossOrder, h]

/-- Positions in `I` on the left of the middle whose mirror lies on the right. -/
noncomputable def leftMirrorCrossingPositions (k : ℕ) (I : PositionInterval (2 * k)) :
    Finset (Fin (2 * k)) := by
  classical
  exact I.toFinset.filter fun p => p.val < k ∧ p.val ≤ I.lo + I.hi - k

theorem leftMirrorCrossingPositions_card_eq_crossOrder_of_crossing {k : ℕ}
    (I : PositionInterval (2 * k)) (hcross : I.lo < k ∧ k ≤ I.hi) :
    (leftMirrorCrossingPositions k I).card = I.crossOrder k := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  by_cases hle : k - I.lo ≤ I.hi + 1 - k
  · have hmap :
        (leftMirrorCrossingPositions k I).map e = Finset.Icc I.lo (k - 1) := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
        rw [leftMirrorCrossingPositions, Finset.mem_filter, mem_toFinset] at hp
        simp [e] at hpval
        subst n
        exact Finset.mem_Icc.mpr ⟨hp.1.1, Nat.le_sub_one_of_lt hp.2.1⟩
      · intro hn
        rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
        have hnlt_k : n < k := by omega
        have hnlt : n < 2 * k := by omega
        have hbound : k - 1 ≤ I.lo + I.hi - k := by omega
        refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
        · rw [leftMirrorCrossingPositions, Finset.mem_filter, mem_toFinset]
          exact ⟨⟨hlo, le_trans hnlt_k.le hcross.2⟩, hnlt_k, le_trans hhi hbound⟩
        · simp [e]
    have hcard_map :
        ((leftMirrorCrossingPositions k I).map e).card =
          (leftMirrorCrossingPositions k I).card :=
      Finset.card_map e
    rw [hmap] at hcard_map
    rw [← hcard_map, crossOrder_eq_min_of_crossing hcross]
    have hmin : Nat.min (k - I.lo) (I.hi + 1 - k) = k - I.lo :=
      Nat.min_eq_left hle
    rw [hmin]
    simp
    omega
  · have hle' : I.hi + 1 - k < k - I.lo := Nat.lt_of_not_ge hle
    have hmap :
        (leftMirrorCrossingPositions k I).map e = Finset.Icc I.lo (I.lo + I.hi - k) := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
        rw [leftMirrorCrossingPositions, Finset.mem_filter, mem_toFinset] at hp
        simp [e] at hpval
        subst n
        exact Finset.mem_Icc.mpr ⟨hp.1.1, hp.2.2⟩
      · intro hn
        rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
        have hbound : I.lo + I.hi - k < k := by omega
        have hnlt_k : n < k := lt_of_le_of_lt hhi hbound
        have hklt : k < 2 * k := by omega
        have hnlt : n < 2 * k := lt_trans hnlt_k hklt
        have hupper : I.lo + I.hi - k ≤ I.hi := by omega
        refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
        · rw [leftMirrorCrossingPositions, Finset.mem_filter, mem_toFinset]
          exact ⟨⟨hlo, le_trans hhi hupper⟩, hnlt_k, hhi⟩
        · simp [e]
    have hcard_map :
        ((leftMirrorCrossingPositions k I).map e).card =
          (leftMirrorCrossingPositions k I).card :=
      Finset.card_map e
    rw [hmap] at hcard_map
    rw [← hcard_map, crossOrder_eq_min_of_crossing hcross]
    have hmin : Nat.min (k - I.lo) (I.hi + 1 - k) = I.hi + 1 - k :=
      Nat.min_eq_right hle'.le
    rw [hmin]
    simp
    omega

/-- Positions in `I` on the right of the middle whose mirror lies on the left. -/
noncomputable def rightMirrorCrossingPositions (k : ℕ) (I : PositionInterval (2 * k)) :
    Finset (Fin (2 * k)) := by
  classical
  exact I.toFinset.filter fun p => k ≤ p.val ∧ I.lo + I.hi + 1 - k ≤ p.val

theorem rightMirrorCrossingPositions_card_eq_crossOrder_of_crossing {k : ℕ}
    (I : PositionInterval (2 * k)) (hcross : I.lo < k ∧ k ≤ I.hi) :
    (rightMirrorCrossingPositions k I).card = I.crossOrder k := by
  classical
  let e : Fin (2 * k) ↪ ℕ := ⟨Fin.val, by intro a b h; exact Fin.ext h⟩
  by_cases hle : k - I.lo ≤ I.hi + 1 - k
  · have hmap :
        (rightMirrorCrossingPositions k I).map e =
          Finset.Icc (I.lo + I.hi + 1 - k) I.hi := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
        rw [rightMirrorCrossingPositions, Finset.mem_filter, mem_toFinset] at hp
        simp [e] at hpval
        subst n
        exact Finset.mem_Icc.mpr ⟨hp.2.2, hp.1.2⟩
      · intro hn
        rcases Finset.mem_Icc.mp hn with ⟨hlo, hhi⟩
        have hlow_ge_k : k ≤ I.lo + I.hi + 1 - k := by omega
        have hnlt : n < 2 * k := lt_of_le_of_lt hhi I.hi_lt
        refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
        · rw [rightMirrorCrossingPositions, Finset.mem_filter, mem_toFinset]
          exact ⟨⟨le_trans hcross.1.le (le_trans hlow_ge_k hlo), hhi⟩,
            le_trans hlow_ge_k hlo, hlo⟩
        · simp [e]
    have hcard_map :
        ((rightMirrorCrossingPositions k I).map e).card =
          (rightMirrorCrossingPositions k I).card :=
      Finset.card_map e
    rw [hmap] at hcard_map
    rw [← hcard_map, crossOrder_eq_min_of_crossing hcross]
    have hmin : Nat.min (k - I.lo) (I.hi + 1 - k) = k - I.lo :=
      Nat.min_eq_left hle
    rw [hmin]
    simp
    omega
  · have hle' : I.hi + 1 - k < k - I.lo := Nat.lt_of_not_ge hle
    have hmap :
        (rightMirrorCrossingPositions k I).map e = Finset.Icc k I.hi := by
      ext n
      constructor
      · intro hn
        rcases Finset.mem_map.mp hn with ⟨p, hp, hpval⟩
        rw [rightMirrorCrossingPositions, Finset.mem_filter, mem_toFinset] at hp
        simp [e] at hpval
        subst n
        exact Finset.mem_Icc.mpr ⟨hp.2.1, hp.1.2⟩
      · intro hn
        rcases Finset.mem_Icc.mp hn with ⟨hk, hhi⟩
        have hthreshold_le_k : I.lo + I.hi + 1 - k ≤ k := by omega
        have hnlt : n < 2 * k := lt_of_le_of_lt hhi I.hi_lt
        refine Finset.mem_map.mpr ⟨⟨n, hnlt⟩, ?_, ?_⟩
        · rw [rightMirrorCrossingPositions, Finset.mem_filter, mem_toFinset]
          exact ⟨⟨le_trans hcross.1.le hk, hhi⟩, hk, le_trans hthreshold_le_k hk⟩
        · simp [e]
    have hcard_map :
        ((rightMirrorCrossingPositions k I).map e).card =
          (rightMirrorCrossingPositions k I).card :=
      Finset.card_map e
    rw [hmap] at hcard_map
    rw [← hcard_map, crossOrder_eq_min_of_crossing hcross]
    have hmin : Nat.min (k - I.lo) (I.hi + 1 - k) = I.hi + 1 - k :=
      Nat.min_eq_right hle'.le
    rw [hmin]
    simp

/-- Positions in `I` whose interval mirror crosses the middle barrier. -/
noncomputable def mirrorCrossingPositions (k : ℕ) (I : PositionInterval (2 * k)) :
    Finset (Fin (2 * k)) :=
  leftMirrorCrossingPositions k I ∪ rightMirrorCrossingPositions k I

theorem left_right_mirrorCrossingPositions_disjoint {k : ℕ}
    (I : PositionInterval (2 * k)) :
    Disjoint (leftMirrorCrossingPositions k I) (rightMirrorCrossingPositions k I) := by
  classical
  rw [Finset.disjoint_left]
  intro p hp_left hp_right
  rw [leftMirrorCrossingPositions, Finset.mem_filter] at hp_left
  rw [rightMirrorCrossingPositions, Finset.mem_filter] at hp_right
  exact not_lt_of_ge hp_right.2.1 hp_left.2.1

theorem mirrorCrossingPositions_card_eq_two_mul_crossOrder_of_crossing {k : ℕ}
    (I : PositionInterval (2 * k)) (hcross : I.lo < k ∧ k ≤ I.hi) :
    (mirrorCrossingPositions k I).card = 2 * I.crossOrder k := by
  classical
  rw [mirrorCrossingPositions, Finset.card_union_of_disjoint
    (left_right_mirrorCrossingPositions_disjoint I)]
  rw [leftMirrorCrossingPositions_card_eq_crossOrder_of_crossing I hcross,
    rightMirrorCrossingPositions_card_eq_crossOrder_of_crossing I hcross]
  omega

















/-- The `d` positions immediately to the left of the middle barrier. -/
noncomputable def leftBarrierPositions (k d : ℕ) : Finset (Fin (2 * k)) := by
  classical
  exact Finset.univ.filter fun p => k - d ≤ p.val ∧ p.val < k

/-- The `d` positions immediately to the right of the middle barrier. -/
noncomputable def rightBarrierPositions (k d : ℕ) : Finset (Fin (2 * k)) := by
  classical
  exact Finset.univ.filter fun p => k ≤ p.val ∧ p.val < k + d

/-- The `2d` positions centered at the middle barrier. -/
noncomputable def centralBarrierPositions (k d : ℕ) : Finset (Fin (2 * k)) :=
  leftBarrierPositions k d ∪ rightBarrierPositions k d

































theorem crossOrder_pos_iff {k : ℕ} (I : PositionInterval (2 * k)) :
    0 < I.crossOrder k ↔ I.lo < k ∧ k ≤ I.hi := by
  constructor
  · intro hpos
    by_contra hcross
    have hzero := crossOrder_eq_zero_of_not_crossing (I := I) hcross
    omega
  · intro hcross
    rw [crossOrder_eq_min_of_crossing hcross]
    have hleft : 0 < k - I.lo := by omega
    have hright : 0 < I.hi + 1 - k := by omega
    exact Nat.lt_min.mpr ⟨hleft, hright⟩





end PositionInterval

/--
A simultaneous move reverses several pairwise-disjoint consecutive blocks.
The actual permutation is kept as data; later lemmas prove its middle-barrier
crossing count from the block fields.
-/
structure BlockMove (N : ℕ) where
  blockCount : ℕ
  blockCount_pos : 0 < blockCount
  block : Fin blockCount → PositionInterval N
  pairwise_disjoint :
    ((Finset.univ : Finset (Fin blockCount)) : Set (Fin blockCount)).PairwiseDisjoint
      (fun i => (block i).toSet)
  nontrivial : ∀ i : Fin blockCount, 2 ≤ (block i).length
  map : State N

namespace BlockMove



/--
Semantic predicate for a block move: inside each block the map is the interval
mirror, and outside all blocks it fixes positions.
-/
def ReversesBlocks {N : ℕ} (M : BlockMove N) : Prop :=
  (∀ i : Fin M.blockCount, ∀ p : Fin N, ∀ hp : (M.block i).Mem p,
    M.map p = (M.block i).mirror p hp) ∧
  ∀ p : Fin N, (∀ i : Fin M.blockCount, ¬ (M.block i).Mem p) → M.map p = p

theorem map_mem_of_reversesBlocks {N : ℕ} {M : BlockMove N}
    (hM : M.ReversesBlocks) {i : Fin M.blockCount} {p : Fin N}
    (hp : (M.block i).Mem p) :
    (M.block i).Mem (M.map p) := by
  rw [hM.1 i p hp]
  exact (M.block i).mirror_mem p hp

theorem map_map_eq_of_reversesBlocks_mem {N : ℕ} {M : BlockMove N}
    (hM : M.ReversesBlocks) {i : Fin M.blockCount} {p : Fin N}
    (hp : (M.block i).Mem p) :
    M.map (M.map p) = p := by
  have hmap : M.map p = (M.block i).mirror p hp := hM.1 i p hp
  have hpmap : (M.block i).Mem (M.map p) := map_mem_of_reversesBlocks hM hp
  have hvalmap : (M.map p).val = (M.block i).lo + (M.block i).hi - p.val :=
    congrArg Fin.val hmap
  apply Fin.ext
  rw [hM.1 i (M.map p) hpmap]
  dsimp [PositionInterval.mirror]
  rcases hp with ⟨hlo, hhi⟩
  omega

theorem map_map_eq_of_reversesBlocks {N : ℕ} {M : BlockMove N}
    (hM : M.ReversesBlocks) (p : Fin N) :
    M.map (M.map p) = p := by
  classical
  by_cases hp : ∃ i : Fin M.blockCount, (M.block i).Mem p
  · rcases hp with ⟨i, hi⟩
    exact map_map_eq_of_reversesBlocks_mem hM hi
  · have hfix : M.map p = p := hM.2 p (by
      intro i
      exact fun hi => hp ⟨i, hi⟩)
    rw [hfix]
    exact hfix







/-- In a disjoint block move, at most one block can cross the middle barrier. -/
theorem crossing_blocks_eq {k : ℕ} (M : BlockMove (2 * k))
    {i j : Fin M.blockCount}
    (hi : (M.block i).lo < k ∧ k ≤ (M.block i).hi)
    (hj : (M.block j).lo < k ∧ k ≤ (M.block j).hi) :
    i = j := by
  by_contra hij
  have hklt : k < 2 * k := lt_of_le_of_lt hi.2 (M.block i).hi_lt
  let p : Fin (2 * k) := ⟨k, hklt⟩
  have hpi : p ∈ (M.block i).toSet := by
    exact ⟨hi.1.le, hi.2⟩
  have hpj : p ∈ (M.block j).toSet := by
    exact ⟨hj.1.le, hj.2⟩
  have hdis : Disjoint ((M.block i).toSet) ((M.block j).toSet) :=
    M.pairwise_disjoint (by simp) (by simp) hij
  exact hdis.le_bot ⟨hpi, hpj⟩

end BlockMove

/-! ### BlockMove from level function -/

noncomputable def levelBlockMoveInterval {N : ℕ} (g : Fin N → ℝ) (p : Fin N)
    (hp : (levelBlockLo g p).val < (levelBlockHi g p).val) :
    PositionInterval N where
  lo := (levelBlockLo g p).val
  hi := (levelBlockHi g p).val
  lo_le_hi := le_of_lt hp
  hi_lt := (levelBlockHi g p).isLt



theorem levelBlockMoveInterval_disjoint {N : ℕ} {g : Fin N → ℝ} (hg : Monotone g)
    {p q : Fin N}
    (hp : (levelBlockLo g p).val < (levelBlockHi g p).val)
    (hq : (levelBlockLo g q).val < (levelBlockHi g q).val)
    (hne : g p ≠ g q) :
    Disjoint (levelBlockMoveInterval g p hp).toSet (levelBlockMoveInterval g q hq).toSet := by
  intro S hSp hSq
  simp only [Set.le_eq_subset, Set.bot_eq_empty, Set.subset_empty_iff]
  ext x; simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  have hxp := hSp hx
  have hxq := hSq hx
  simp [PositionInterval.toSet, PositionInterval.Mem, levelBlockMoveInterval] at hxp hxq
  have h1 := monotone_levelBlock_eq hg (Fin.le_def.mpr hxp.1) (Fin.le_def.mpr hxp.2)
  have h2 := monotone_levelBlock_eq hg (Fin.le_def.mpr hxq.1) (Fin.le_def.mpr hxq.2)
  exact hne (h1.symm.trans h2)

/--
One legal step of a generalized allowable sequence.  The increasing-block
condition is the finite Goodman--Pollack/Ungar rule before reversal.
-/
structure ReversalStep (k : ℕ) (π ρ : State (2 * k)) where
  move : BlockMove (2 * k)
  step_apply : ∀ p : Fin (2 * k), ρ p = π (move.map p)
  increasing_before :
    ∀ i : Fin move.blockCount,
      StrictMonoOn (fun p : Fin (2 * k) => (π p).val) ((move.block i).toSet)

namespace ReversalStep

/-- The total middle-barrier order of a reversal step. -/
def order {k : ℕ} {π ρ : State (2 * k)} (M : ReversalStep k π ρ) : ℕ :=
  ∑ i : Fin M.move.blockCount, (M.move.block i).crossOrder k

/-- A reversal step is crossing exactly when its total order is positive. -/
def IsCrossing {k : ℕ} {π ρ : State (2 * k)} (M : ReversalStep k π ρ) : Prop :=
  0 < M.order



/-- A state is strictly decreasing on a finite set of positions. -/
def DecreasingOnPositions {N : ℕ} (π : State N) (s : Finset (Fin N)) : Prop :=
  ∀ ⦃p⦄, p ∈ s → ∀ ⦃q⦄, q ∈ s → p < q → (π q).val < (π p).val

/-- A state is strictly increasing on a finite set of positions. -/
def IncreasingOnPositions {N : ℕ} (π : State N) (s : Finset (Fin N)) : Prop :=
  ∀ ⦃p⦄, p ∈ s → ∀ ⦃q⦄, q ∈ s → p < q → (π p).val < (π q).val





























































theorem isCrossing_iff_exists_crossing_block {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) :
    M.IsCrossing ↔
      ∃ i : Fin M.move.blockCount, (M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi := by
  classical
  unfold IsCrossing order
  rw [Finset.sum_pos_iff]
  constructor
  · rintro ⟨i, _hi, hpos⟩
    exact ⟨i, (M.move.block i).crossOrder_pos_iff.mp hpos⟩
  · rintro ⟨i, hcross⟩
    exact ⟨i, by simp, (M.move.block i).crossOrder_pos_iff.mpr hcross⟩

theorem order_eq_crossOrder_of_crossing_block {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) {i : Fin M.move.blockCount}
    (hi : (M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi) :
    M.order = (M.move.block i).crossOrder k := by
  classical
  unfold order
  rw [Finset.sum_eq_single i]
  · intro j _hj hji
    have hnot : ¬ ((M.move.block j).lo < k ∧ k ≤ (M.move.block j).hi) := by
      intro hjcross
      exact hji ((M.move.crossing_blocks_eq hi hjcross).symm)
    exact PositionInterval.crossOrder_eq_zero_of_not_crossing hnot
  · intro hi_not
    exact False.elim (hi_not (by simp))

noncomputable def crossingBlockIndex {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) : Fin M.move.blockCount :=
  Classical.choose (M.isCrossing_iff_exists_crossing_block.mp hM)

theorem crossingBlockIndex_spec {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    (M.move.block (M.crossingBlockIndex hM)).lo < k ∧
      k ≤ (M.move.block (M.crossingBlockIndex hM)).hi :=
  Classical.choose_spec (M.isCrossing_iff_exists_crossing_block.mp hM)

theorem crossingBlockIndex_unique {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) {i : Fin M.move.blockCount}
    (hi : (M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi) :
    i = M.crossingBlockIndex hM :=
  M.move.crossing_blocks_eq hi (M.crossingBlockIndex_spec hM)

theorem order_eq_crossingBlockIndex_crossOrder {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hM : M.IsCrossing) :
    M.order = (M.move.block (M.crossingBlockIndex hM)).crossOrder k :=
  M.order_eq_crossOrder_of_crossing_block (M.crossingBlockIndex_spec hM)





























































theorem new_position_eq_map_old_position_of_reversesBlocks {k : ℕ}
    {π ρ : State (2 * k)} (M : ReversalStep k π ρ)
    (hrev : M.move.ReversesBlocks) (a : Fin (2 * k)) :
    ρ.symm a = M.move.map (π.symm a) := by
  apply ρ.injective
  rw [Equiv.apply_symm_apply]
  rw [M.step_apply]
  rw [M.move.map_map_eq_of_reversesBlocks hrev]
  exact (Equiv.apply_symm_apply π a).symm

theorem crossesMiddle_iff_map_old_position {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (a : Fin (2 * k)) :
    crossesMiddle k π ρ a ↔
      (middleLeft k (π.symm a) ↔ ¬ middleLeft k (M.move.map (π.symm a))) := by
  rw [crossesMiddle, M.new_position_eq_map_old_position_of_reversesBlocks hrev a]





noncomputable def positionCrossingCard (k : ℕ) (σ : State (2 * k)) : ℕ := by
  classical
  exact Fintype.card {p : Fin (2 * k) // middleLeft k p ↔ ¬ middleLeft k (σ p)}

noncomputable def labelCrossingCard (k : ℕ) (π ρ : State (2 * k)) : ℕ := by
  classical
  exact Fintype.card {a : Fin (2 * k) // crossesMiddle k π ρ a}

theorem crossingLabelsCard_eq_positionCrossingCard_of_reversesBlocks {k : ℕ}
    {π ρ : State (2 * k)} (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) :
    labelCrossingCard k π ρ = positionCrossingCard k M.move.map := by
  classical
  unfold labelCrossingCard positionCrossingCard
  refine Fintype.card_congr ?_
  refine
  { toFun := fun a =>
      ⟨π.symm a.1, (M.crossesMiddle_iff_map_old_position hrev a.1).mp a.2⟩
    invFun := fun p =>
      ⟨π p.1, (M.crossesMiddle_iff_map_old_position hrev (π p.1)).mpr ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa using p.2
  · intro a
    apply Subtype.ext
    exact Equiv.apply_symm_apply π a.1
  · intro p
    apply Subtype.ext
    exact Equiv.symm_apply_apply π p.1

theorem positionCrossingCard_eq_zero_of_no_crossing_block {k : ℕ}
    {M : BlockMove (2 * k)} (hrev : M.ReversesBlocks)
    (hnone : ∀ i : Fin M.blockCount, ¬ ((M.block i).lo < k ∧ k ≤ (M.block i).hi)) :
    positionCrossingCard k M.map = 0 := by
  classical
  unfold positionCrossingCard
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun x => ?_⟩
  rcases x with ⟨p, hp⟩
  by_cases hmem : ∃ i : Fin M.blockCount, (M.block i).Mem p
  · rcases hmem with ⟨i, hpi⟩
    have hpmap : (M.block i).Mem (M.map p) :=
      M.map_mem_of_reversesBlocks hrev hpi
    have hside : (M.block i).hi < k ∨ k ≤ (M.block i).lo := by
      have hlohi := (M.block i).lo_le_hi
      have hnot := hnone i
      omega
    rcases hside with hleft | hright
    · have hp_left : middleLeft k p := by
        exact lt_of_le_of_lt hpi.2 hleft
      have hmap_left : middleLeft k (M.map p) := by
        exact lt_of_le_of_lt hpmap.2 hleft
      exact (hp.mp hp_left) hmap_left
    · have hp_not_left : ¬ middleLeft k p := by
        intro hp_left
        exact not_lt_of_ge (le_trans hright hpi.1) hp_left
      have hmap_not_left : ¬ middleLeft k (M.map p) := by
        intro hmap_left
        exact not_lt_of_ge (le_trans hright hpmap.1) hmap_left
      exact hp_not_left (hp.mpr hmap_not_left)
  · have hfix : M.map p = p := hrev.2 p (by
      intro i
      exact fun hi => hmem ⟨i, hi⟩)
    rw [hfix] at hp
    by_cases hp_left : middleLeft k p
    · exact (hp.mp hp_left) hp_left
    · exact hp_left (hp.mpr hp_left)



theorem exists_mem_crossing_block_of_position_crosses {k : ℕ}
    {M : BlockMove (2 * k)} (hrev : M.ReversesBlocks) {p : Fin (2 * k)}
    (hp : middleLeft k p ↔ ¬ middleLeft k (M.map p)) :
    ∃ i : Fin M.blockCount,
      (M.block i).Mem p ∧ (M.block i).lo < k ∧ k ≤ (M.block i).hi := by
  classical
  by_cases hmem : ∃ i : Fin M.blockCount, (M.block i).Mem p
  · rcases hmem with ⟨i, hpi⟩
    refine ⟨i, hpi, ?_⟩
    by_contra hnotcross
    have hpmap : (M.block i).Mem (M.map p) :=
      M.map_mem_of_reversesBlocks hrev hpi
    have hside : (M.block i).hi < k ∨ k ≤ (M.block i).lo := by
      have hlohi := (M.block i).lo_le_hi
      omega
    rcases hside with hleft | hright
    · have hp_left : middleLeft k p := lt_of_le_of_lt hpi.2 hleft
      have hmap_left : middleLeft k (M.map p) := lt_of_le_of_lt hpmap.2 hleft
      exact (hp.mp hp_left) hmap_left
    · have hp_not_left : ¬ middleLeft k p := by
        intro hp_left
        exact not_lt_of_ge (le_trans hright hpi.1) hp_left
      have hmap_not_left : ¬ middleLeft k (M.map p) := by
        intro hmap_left
        exact not_lt_of_ge (le_trans hright hpmap.1) hmap_left
      exact hp_not_left (hp.mpr hmap_not_left)
  · have hfix : M.map p = p := hrev.2 p (by
      intro i hi
      exact hmem ⟨i, hi⟩)
    rw [hfix] at hp
    by_cases hleft : middleLeft k p
    · exact False.elim ((hp.mp hleft) hleft)
    · exact False.elim (hleft (hp.mpr hleft))

theorem position_crosses_mem_crossingBlockIndex {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing)
    {p : Fin (2 * k)}
    (hp : middleLeft k p ↔ ¬ middleLeft k (M.move.map p)) :
    (M.move.block (M.crossingBlockIndex hM)).Mem p := by
  rcases exists_mem_crossing_block_of_position_crosses (M := M.move) hrev hp with
    ⟨i, hpi, hcross⟩
  have hi : i = M.crossingBlockIndex hM :=
    M.crossingBlockIndex_unique hM hcross
  rwa [hi] at hpi



theorem positionCrossingCard_eq_two_mul_order_of_reversesBlocks {k : ℕ}
    {π ρ : State (2 * k)} (M : ReversalStep k π ρ)
    (hrev : M.move.ReversesBlocks) (hM : M.IsCrossing) :
    positionCrossingCard k M.move.map = 2 * M.order := by
  classical
  let B := M.move.block (M.crossingBlockIndex hM)
  have hBcross : B.lo < k ∧ k ≤ B.hi :=
    M.crossingBlockIndex_spec hM
  have hcard :
      positionCrossingCard k M.move.map =
        (B.mirrorCrossingPositions k).card := by
    have hcardSubtype :
        Fintype.card
          {p : Fin (2 * k) // middleLeft k p ↔ ¬ middleLeft k (M.move.map p)} =
          Fintype.card {p : Fin (2 * k) // p ∈ B.mirrorCrossingPositions k} := by
      refine Fintype.card_congr ?_
      refine
      { toFun := ?_
        invFun := ?_
        left_inv := ?_
        right_inv := ?_ }
      · intro p
        refine ⟨p.1, ?_⟩
        have hpB : B.Mem p.1 :=
        M.position_crosses_mem_crossingBlockIndex hrev hM p.2
        by_cases hleft : middleLeft k p.1
        · have hmap_not_left : ¬ middleLeft k (M.move.map p.1) := p.2.mp hleft
          have hmap_eq : M.move.map p.1 = B.mirror p.1 hpB :=
            hrev.1 (M.crossingBlockIndex hM) p.1 hpB
          have hmirror_right : k ≤ (B.mirror p.1 hpB).val := by
            rw [← hmap_eq]
            exact not_lt.mp hmap_not_left
          have hle_sub : p.1.val ≤ B.lo + B.hi - k :=
            (B.le_mirror_iff_le_sub p.1 hpB hBcross.2).mp hmirror_right
          rw [PositionInterval.mirrorCrossingPositions, Finset.mem_union,
            PositionInterval.leftMirrorCrossingPositions,
            PositionInterval.rightMirrorCrossingPositions, Finset.mem_filter,
            Finset.mem_filter, PositionInterval.mem_toFinset]
          exact Or.inl ⟨hpB, hleft, hle_sub⟩
        · have hp_right : k ≤ p.1.val := not_lt.mp hleft
          have hmap_left : middleLeft k (M.move.map p.1) := by
            by_contra hmap_not_left
            exact hleft (p.2.mpr hmap_not_left)
          have hmap_eq : M.move.map p.1 = B.mirror p.1 hpB :=
            hrev.1 (M.crossingBlockIndex hM) p.1 hpB
          have hmirror_left : (B.mirror p.1 hpB).val < k := by
            rw [← hmap_eq]
            exact hmap_left
          have hthreshold : B.lo + B.hi + 1 - k ≤ p.1.val := by
            rw [B.mirror_lt_iff_sub_lt p.1 hpB] at hmirror_left
            rcases hpB with ⟨hlo, hhi⟩
            omega
          rw [PositionInterval.mirrorCrossingPositions, Finset.mem_union,
            PositionInterval.leftMirrorCrossingPositions,
            PositionInterval.rightMirrorCrossingPositions, Finset.mem_filter,
            Finset.mem_filter, PositionInterval.mem_toFinset]
          exact Or.inr ⟨hpB, hp_right, hthreshold⟩
      · intro p
        refine ⟨p.1, ?_⟩
        have hp_mem : p.1 ∈ B.mirrorCrossingPositions k := p.2
        simp [PositionInterval.mirrorCrossingPositions,
          PositionInterval.leftMirrorCrossingPositions,
          PositionInterval.rightMirrorCrossingPositions,
          PositionInterval.mem_toFinset] at hp_mem
        rcases hp_mem with hp_left | hp_right
        · rcases hp_left with ⟨hpB, hp_left, hle_sub⟩
          have hmap_eq : M.move.map p.1 = B.mirror p.1 hpB :=
            hrev.1 (M.crossingBlockIndex hM) p.1 hpB
          have hmirror_right : k ≤ (B.mirror p.1 hpB).val :=
            (B.le_mirror_iff_le_sub p.1 hpB hBcross.2).mpr hle_sub
          have hmap_not_left : ¬ middleLeft k (M.move.map p.1) := by
            rw [hmap_eq]
            exact not_lt.mpr hmirror_right
          exact iff_of_true hp_left hmap_not_left
        · rcases hp_right with ⟨hpB, hp_right, hthreshold⟩
          have hmap_eq : M.move.map p.1 = B.mirror p.1 hpB :=
            hrev.1 (M.crossingBlockIndex hM) p.1 hpB
          have hmirror_left : (B.mirror p.1 hpB).val < k := by
            rw [B.mirror_lt_iff_sub_lt p.1 hpB]
            rcases hpB with ⟨hlo, hhi⟩
            omega
          have hp_not_left : ¬ middleLeft k p.1 := not_lt.mpr hp_right
          have hmap_left : middleLeft k (M.move.map p.1) := by
            rw [hmap_eq]
            exact hmirror_left
          exact iff_of_false hp_not_left (not_not.mpr hmap_left)
      · intro p
        apply Subtype.ext
        rfl
      · intro p
        apply Subtype.ext
        rfl
    have hfinset :
        Fintype.card {p : Fin (2 * k) // p ∈ B.mirrorCrossingPositions k} =
          (B.mirrorCrossingPositions k).card := by
      simp
    exact (by
      simpa [positionCrossingCard] using hcardSubtype.trans hfinset)
  rw [hcard]
  rw [B.mirrorCrossingPositions_card_eq_two_mul_crossOrder_of_crossing hBcross]
  rw [M.order_eq_crossingBlockIndex_crossOrder hM]















end ReversalStep

/-- The number of labels crossing the middle barrier in one concrete step. -/
noncomputable def stepCrossingLabelsCard (k : ℕ) (π ρ : State (2 * k)) : ℕ := by
  classical
  exact Fintype.card {a : Fin (2 * k) // crossesMiddle k π ρ a}

theorem stepCrossingLabelsCard_relabel {k : ℕ}
    (π ρ τ : State (2 * k)) :
    stepCrossingLabelsCard k (π.trans τ.symm) (ρ.trans τ.symm) =
      stepCrossingLabelsCard k π ρ := by
  classical
  unfold stepCrossingLabelsCard
  refine Fintype.card_congr ?_
  refine
    { toFun := fun x => ⟨τ x.1, (crossesMiddle_relabel π ρ τ x.1).mp x.2⟩
      invFun := fun x => ⟨τ.symm x.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hx := (crossesMiddle_relabel π ρ τ (τ.symm x.1)).mpr (by simpa using x.2)
    simpa using hx
  · intro x
    simp
  · intro x
    simp

theorem stepCrossingLabelsCard_reverse_left {k : ℕ}
    (π ρ : State (2 * k)) :
    stepCrossingLabelsCard k ((reverseFin (2 * k)).trans π)
        ((reverseFin (2 * k)).trans ρ) =
      stepCrossingLabelsCard k π ρ := by
  classical
  unfold stepCrossingLabelsCard
  refine Fintype.card_congr ?_
  refine
    { toFun := fun x => ⟨x.1, (crossesMiddle_reverse_left π ρ x.1).mp x.2⟩
      invFun := fun x => ⟨x.1, (crossesMiddle_reverse_left π ρ x.1).mpr x.2⟩
      left_inv := ?_
      right_inv := ?_ } <;>
    intro x <;>
    simp

theorem stepCrossingLabelsCard_reverse_left_relabel {k : ℕ}
    (π ρ τ : State (2 * k)) :
    stepCrossingLabelsCard k
        (((reverseFin (2 * k)).trans π).trans τ.symm)
        (((reverseFin (2 * k)).trans ρ).trans τ.symm) =
      stepCrossingLabelsCard k π ρ := by
  rw [stepCrossingLabelsCard_relabel]
  exact stepCrossingLabelsCard_reverse_left π ρ

theorem stepCrossingLabelsCard_eq_labelCrossingCard
    (k : ℕ) (π ρ : State (2 * k)) :
    stepCrossingLabelsCard k π ρ = ReversalStep.labelCrossingCard k π ρ := by
  classical
  simp [stepCrossingLabelsCard, ReversalStep.labelCrossingCard]

theorem stepCrossingLabelsCard_eq_positionCrossingCard_of_reversesBlocks {k : ℕ}
    {π ρ : State (2 * k)} (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) :
    stepCrossingLabelsCard k π ρ = ReversalStep.positionCrossingCard k M.move.map := by
  rw [stepCrossingLabelsCard_eq_labelCrossingCard]
  exact M.crossingLabelsCard_eq_positionCrossingCard_of_reversesBlocks hrev

theorem crossed_labels_card_of_reversesBlocks {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) :
    stepCrossingLabelsCard k π ρ = 2 * M.order := by
  by_cases hM : M.IsCrossing
  · rw [stepCrossingLabelsCard_eq_positionCrossingCard_of_reversesBlocks M hrev]
    exact M.positionCrossingCard_eq_two_mul_order_of_reversesBlocks hrev hM
  · have horder : M.order = 0 := by
      unfold ReversalStep.IsCrossing at hM
      omega
    have hnone :
        ∀ i : Fin M.move.blockCount,
          ¬ ((M.move.block i).lo < k ∧ k ≤ (M.move.block i).hi) := by
      intro i hi
      exact hM ((M.isCrossing_iff_exists_crossing_block).mpr ⟨i, hi⟩)
    have hzero := ReversalStep.positionCrossingCard_eq_zero_of_no_crossing_block
      (k := k) (M := M.move) hrev hnone
    rw [stepCrossingLabelsCard_eq_positionCrossingCard_of_reversesBlocks M hrev,
      hzero, horder]

/--
A reversal step together with the key finite counting theorem for that step.
The block-reversal geometry should eventually prove this field.
-/
structure CountedReversalStep (k : ℕ) (π ρ : State (2 * k)) extends
    ReversalStep k π ρ where
  crossed_labels_card : stepCrossingLabelsCard k π ρ = 2 * toReversalStep.order

noncomputable def CountedReversalStep.ofReversesBlocks {k : ℕ} {π ρ : State (2 * k)}
    (M : ReversalStep k π ρ) (hrev : M.move.ReversesBlocks) :
    CountedReversalStep k π ρ where
  toReversalStep := M
  crossed_labels_card := crossed_labels_card_of_reversesBlocks M hrev

/-- A generalized allowable sequence with counted reversal data on every step. -/
structure CountedGeneralizedAllowableSequence (k r : ℕ) where
  seq : GeneralizedAllowableSequence k r
  step : ∀ j : Fin r, CountedReversalStep k (seq.π (stepFrom j)) (seq.π (stepTo j))

namespace CountedGeneralizedAllowableSequence

noncomputable def ofReversesBlocks {k r : ℕ} (A : GeneralizedAllowableSequence k r)
    (step : ∀ j : Fin r, ReversalStep k (A.π (stepFrom j)) (A.π (stepTo j)))
    (hrev : ∀ j : Fin r, (step j).move.ReversesBlocks) :
    CountedGeneralizedAllowableSequence k r where
  seq := A
  step := fun j => CountedReversalStep.ofReversesBlocks (step j) (hrev j)

/-- Counted reversal steps produce the `StepCounting` data used above. -/
noncomputable def toStepCounting {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r) :
    GeneralizedAllowableSequence.StepCounting A.seq where
  order := fun j => (A.step j).toReversalStep.order
  crossed_labels_card := by
    intro j
    simpa [GeneralizedAllowableSequence.crossingLabelsCard, stepCrossingLabelsCard]
      using (A.step j).crossed_labels_card

def moveOrder {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r) (j : Fin r) : ℕ :=
  (A.step j).toReversalStep.order

def IsCrossing {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r) (j : Fin r) : Prop :=
  0 < A.moveOrder j

def ConsecutiveCrossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (i j : Fin r) : Prop :=
  A.IsCrossing i ∧ A.IsCrossing j ∧ i.val < j.val ∧
    ∀ l : Fin r, i.val < l.val → l.val < j.val → ¬ A.IsCrossing l





noncomputable def crossingMoves {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter A.IsCrossing

theorem mem_crossingMoves {k r : ℕ} {A : CountedGeneralizedAllowableSequence k r}
    {j : Fin r} :
    j ∈ A.crossingMoves ↔ A.IsCrossing j := by
  classical
  simp [crossingMoves]

theorem crossingLabelsCard_eq_two_mul_moveOrder {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (j : Fin r) :
    GeneralizedAllowableSequence.crossingLabelsCard A.seq j = 2 * A.moveOrder j := by
  exact A.toStepCounting.crossed_labels_card j

theorem moveOrder_eq_of_crossingLabelsCard_eq {k r s : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (B : CountedGeneralizedAllowableSequence k s)
    {i : Fin r} {j : Fin s}
    (hcard :
      GeneralizedAllowableSequence.crossingLabelsCard A.seq i =
        GeneralizedAllowableSequence.crossingLabelsCard B.seq j) :
    A.moveOrder i = B.moveOrder j := by
  have hA := A.crossingLabelsCard_eq_two_mul_moveOrder i
  have hB := B.crossingLabelsCard_eq_two_mul_moveOrder j
  omega

theorem isCrossing_iff_of_crossingLabelsCard_eq {k r s : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (B : CountedGeneralizedAllowableSequence k s)
    {i : Fin r} {j : Fin s}
    (hcard :
      GeneralizedAllowableSequence.crossingLabelsCard A.seq i =
        GeneralizedAllowableSequence.crossingLabelsCard B.seq j) :
    A.IsCrossing i ↔ B.IsCrossing j := by
  rw [IsCrossing, IsCrossing, A.moveOrder_eq_of_crossingLabelsCard_eq B hcard]









theorem letters_cross {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r) :
    2 * k ≤ ∑ j : Fin r, 2 * A.moveOrder j := by
  exact A.toStepCounting.letters_cross

theorem sum_moveOrder_eq_sum_crossingMoves {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) :
    (∑ j : Fin r, 2 * A.moveOrder j) =
      ∑ j ∈ A.crossingMoves, 2 * A.moveOrder j := by
  classical
  exact (Finset.sum_subset (Finset.subset_univ A.crossingMoves) (by
    intro j _hj hnot
    have hnotCross : ¬ A.IsCrossing j := by
      intro hjCross
      exact hnot (A.mem_crossingMoves.mpr hjCross)
    unfold IsCrossing at hnotCross
    have hzero : A.moveOrder j = 0 := by omega
    simp [hzero])).symm

theorem letters_cross_crossingMoves {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) :
    2 * k ≤ ∑ j ∈ A.crossingMoves, 2 * A.moveOrder j := by
  rw [← A.sum_moveOrder_eq_sum_crossingMoves]
  exact A.letters_cross

theorem exists_crossing_move {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r)
    (hk : 0 < k) :
    ∃ j : Fin r, A.IsCrossing j := by
  classical
  let a : Fin (2 * k) := ⟨0, by omega⟩
  rcases A.seq.every_label_crosses a with ⟨j, hj⟩
  refine ⟨j, ?_⟩
  have hcard_pos :
      0 < GeneralizedAllowableSequence.crossingLabelsCard A.seq j := by
    unfold GeneralizedAllowableSequence.crossingLabelsCard
    exact Fintype.card_pos_iff.mpr ⟨⟨a, hj⟩⟩
  have hcount := A.crossingLabelsCard_eq_two_mul_moveOrder j
  unfold IsCrossing
  omega

theorem crossingMoves_nonempty {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r)
    (hk : 0 < k) :
    A.crossingMoves.Nonempty := by
  rcases A.exists_crossing_move hk with ⟨j, hj⟩
  exact ⟨j, A.mem_crossingMoves.mpr hj⟩

theorem crossingMoves_card_pos {k r : ℕ} (A : CountedGeneralizedAllowableSequence k r)
    (hk : 0 < k) :
    0 < A.crossingMoves.card := by
  exact Finset.card_pos.mpr (A.crossingMoves_nonempty hk)

noncomputable def crossingIdx {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) :
    Fin A.crossingMoves.card → Fin r :=
  A.crossingMoves.orderEmbOfFin rfl

theorem crossingIdx_mem {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (i : Fin A.crossingMoves.card) :
    A.crossingIdx i ∈ A.crossingMoves := by
  classical
  simp [crossingIdx]

theorem crossingIdx_isCrossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (i : Fin A.crossingMoves.card) :
    A.IsCrossing (A.crossingIdx i) := by
  exact A.mem_crossingMoves.mp (A.crossingIdx_mem i)

theorem crossingIdx_strict {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) {i j : Fin A.crossingMoves.card}
    (hij : i < j) :
    (A.crossingIdx i).val < (A.crossingIdx j).val := by
  change A.crossingIdx i < A.crossingIdx j
  exact (A.crossingMoves.orderEmbOfFin rfl).strictMono hij



theorem not_isCrossing_before_first_crossingIdx {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (hpos : 0 < A.crossingMoves.card) {j : Fin r}
    (hbefore : j.val < (A.crossingIdx ⟨0, hpos⟩).val) :
    ¬ A.IsCrossing j := by
  classical
  intro hjCross
  have hjmem : j ∈ A.crossingMoves := A.mem_crossingMoves.mpr hjCross
  have hmap :
      Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ =
        A.crossingMoves :=
    Finset.map_orderEmbOfFin_univ A.crossingMoves rfl
  have hjmap : j ∈ Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ := by
    rwa [hmap]
  rcases Finset.mem_map.mp hjmap with ⟨l, _hlmem, hlj⟩
  have hlj' : A.crossingIdx l = j := by
    simpa [crossingIdx] using hlj
  have hfinle : (⟨0, hpos⟩ : Fin A.crossingMoves.card) ≤ l := by
    change 0 ≤ l.val
    omega
  have hidxle : A.crossingIdx ⟨0, hpos⟩ ≤ A.crossingIdx l := by
    change (A.crossingMoves.orderEmbOfFin rfl ⟨0, hpos⟩) ≤
      A.crossingMoves.orderEmbOfFin rfl l
    exact (A.crossingMoves.orderEmbOfFin rfl).monotone hfinle
  have hvaleq : (A.crossingIdx l).val = j.val := congrArg Fin.val hlj'
  have hidxle_val : (A.crossingIdx ⟨0, hpos⟩).val ≤ (A.crossingIdx l).val :=
    hidxle
  omega

theorem not_isCrossing_after_last_crossingIdx {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (hpos : 0 < A.crossingMoves.card) {j : Fin r}
    (hafter : (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩).val < j.val) :
    ¬ A.IsCrossing j := by
  classical
  intro hjCross
  have hjmem : j ∈ A.crossingMoves := A.mem_crossingMoves.mpr hjCross
  have hmap :
      Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ =
        A.crossingMoves :=
    Finset.map_orderEmbOfFin_univ A.crossingMoves rfl
  have hjmap : j ∈ Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ := by
    rwa [hmap]
  rcases Finset.mem_map.mp hjmap with ⟨l, _hlmem, hlj⟩
  have hlj' : A.crossingIdx l = j := by
    simpa [crossingIdx] using hlj
  have hfinle : l ≤ (⟨A.crossingMoves.card - 1, by omega⟩ :
      Fin A.crossingMoves.card) := by
    change l.val ≤ A.crossingMoves.card - 1
    omega
  have hidxle : A.crossingIdx l ≤
      A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩ := by
    change (A.crossingMoves.orderEmbOfFin rfl l) ≤
      A.crossingMoves.orderEmbOfFin rfl ⟨A.crossingMoves.card - 1, by omega⟩
    exact (A.crossingMoves.orderEmbOfFin rfl).monotone hfinle
  have hvaleq : (A.crossingIdx l).val = j.val := congrArg Fin.val hlj'
  have hidxle_val : (A.crossingIdx l).val ≤
      (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩).val :=
    hidxle
  omega







theorem sum_crossingIdx_eq_sum_crossingMoves {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) :
    (∑ i : Fin A.crossingMoves.card, 2 * A.moveOrder (A.crossingIdx i)) =
      ∑ j ∈ A.crossingMoves, 2 * A.moveOrder j := by
  classical
  calc
    (∑ i : Fin A.crossingMoves.card, 2 * A.moveOrder (A.crossingIdx i)) =
        ∑ j ∈ Finset.map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding Finset.univ,
          2 * A.moveOrder j := by
          exact (Finset.univ.sum_map (A.crossingMoves.orderEmbOfFin rfl).toEmbedding
            (fun j => 2 * A.moveOrder j)).symm
    _ = ∑ j ∈ A.crossingMoves, 2 * A.moveOrder j := by
          rw [Finset.map_orderEmbOfFin_univ]

theorem letters_cross_crossingIdx {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) :
    2 * k ≤ ∑ i : Fin A.crossingMoves.card, 2 * A.moveOrder (A.crossingIdx i) := by
  rw [A.sum_crossingIdx_eq_sum_crossingMoves]
  exact A.letters_cross_crossingMoves

theorem crossingMoves_card_ne_one_of_no_full_crossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (hnoFull : ∀ j : Fin r, A.IsCrossing j → A.moveOrder j < k) :
    A.crossingMoves.card ≠ 1 := by
  intro hcard
  have hpos : 0 < A.crossingMoves.card := by omega
  let i0 : Fin A.crossingMoves.card := ⟨0, hpos⟩
  have hall : ∀ i : Fin A.crossingMoves.card, i = i0 := by
    intro i
    apply Fin.ext
    dsimp [i0]
    omega
  have hsum_eq :
      (∑ i : Fin A.crossingMoves.card, 2 * A.moveOrder (A.crossingIdx i)) =
        2 * A.moveOrder (A.crossingIdx i0) := by
    rw [Finset.sum_eq_single i0]
    · intro b _hb hbne
      exact False.elim (hbne (hall b))
    · intro hnot
      exact False.elim (hnot (by simp))
  have hletters := A.letters_cross_crossingIdx
  rw [hsum_eq] at hletters
  have hlt : A.moveOrder (A.crossingIdx i0) < k :=
    hnoFull (A.crossingIdx i0) (A.crossingIdx_isCrossing i0)
  omega

theorem two_le_crossingMoves_card_of_no_full_crossing {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r) (hk : 0 < k)
    (hnoFull : ∀ j : Fin r, A.IsCrossing j → A.moveOrder j < k) :
    2 ≤ A.crossingMoves.card := by
  have hpos := A.crossingMoves_card_pos hk
  by_contra hnot
  have hcard : A.crossingMoves.card = 1 := by omega
  exact A.crossingMoves_card_ne_one_of_no_full_crossing hnoFull hcard

noncomputable def toMoveSchedule {k r : ℕ}
    (A : CountedGeneralizedAllowableSequence k r)
    (htwo : 2 ≤ A.crossingMoves.card)
    (hgap_between :
      ∀ (i : ℕ) (hi : i + 1 < A.crossingMoves.card),
        A.moveOrder (A.crossingIdx ⟨i, by omega⟩) +
            A.moveOrder (A.crossingIdx ⟨i + 1, by omega⟩) - 1 ≤
          (A.crossingIdx ⟨i + 1, by omega⟩).val -
            (A.crossingIdx ⟨i, by omega⟩).val - 1)
    (hgap_ends :
      A.moveOrder (A.crossingIdx ⟨0, by omega⟩) +
          A.moveOrder (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩) - 1 ≤
        (A.crossingIdx ⟨0, by omega⟩).val +
          (r - 1 - (A.crossingIdx ⟨A.crossingMoves.card - 1, by omega⟩).val)) :
    UngarMoveSchedule k r where
  crossingCount := A.crossingMoves.card
  order := fun i => A.moveOrder (A.crossingIdx i)
  letters_cross := A.letters_cross_crossingIdx
  two_le_crossingCount := htwo
  idx := A.crossingIdx
  idx_strict := by
    intro i j hij
    exact A.crossingIdx_strict hij
  order_pos := by
    intro i
    exact A.crossingIdx_isCrossing i
  gap_between := hgap_between
  gap_ends := hgap_ends







end CountedGeneralizedAllowableSequence

/--
A counted generalized allowable sequence that still remembers the concrete
block-reversal semantics of every step.  The counting layer alone is enough
for `letters_cross`; the gap proof needs this pointwise reversal information.
-/
structure ConcreteGeneralizedAllowableSequence (k r : ℕ) extends
    CountedGeneralizedAllowableSequence k r where
  reversesBlocks :
    ∀ j : Fin r, (step j).toReversalStep.move.ReversesBlocks

namespace ConcreteGeneralizedAllowableSequence

def stateAt {k r : ℕ} (A : ConcreteGeneralizedAllowableSequence k r)
    (m : ℕ) (hm : m ≤ r) : State (2 * k) :=
  A.seq.π ⟨m, Nat.lt_succ_of_le hm⟩



def NoDirectFullMove {k r : ℕ} (A : ConcreteGeneralizedAllowableSequence k r) : Prop :=
  ∀ j : Fin r,
    A.seq.π (stepFrom j) ≠ Equiv.refl (Fin (2 * k)) ∨
      A.seq.π (stepTo j) ≠ reverseFin (2 * k)



def DirectFullMoveForcesCommonLevel {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {points : Finset Point2}
    (L : PointLabeling points k) (stepDir : Fin r → Direction) : Prop :=
  ∀ j : Fin r,
    A.seq.π (stepFrom j) = Equiv.refl (Fin (2 * k)) →
      A.seq.π (stepTo j) = reverseFin (2 * k) →
        ∃ c : ℝ, ∀ a : Fin (2 * k), directionLevel (stepDir j) (L.point a) = c



def BlocksHaveCommonLevel {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r) {points : Finset Point2}
    (L : PointLabeling points k) (stepDir : Fin r → Direction) : Prop :=
  ∀ j : Fin r, ∀ b : Fin (A.step j).toReversalStep.move.blockCount,
    ∃ c : ℝ, ∀ p : Fin (2 * k),
      ((A.step j).toReversalStep.move.block b).Mem p →
        directionLevel (stepDir j)
          (L.point (A.seq.π (stepFrom j) p)) = c



















































































def CyclicEndGap {k r : ℕ} (A : ConcreteGeneralizedAllowableSequence k r)
    (hpos : 0 < A.toCountedGeneralizedAllowableSequence.crossingMoves.card) : Prop :=
  A.toCountedGeneralizedAllowableSequence.moveOrder
      (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, hpos⟩) +
      A.toCountedGeneralizedAllowableSequence.moveOrder
        (A.toCountedGeneralizedAllowableSequence.crossingIdx
          ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by omega⟩) - 1 ≤
    (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, hpos⟩).val +
      (r - 1 -
        (A.toCountedGeneralizedAllowableSequence.crossingIdx
          ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by omega⟩).val)

structure CyclicEndGapWitness {k r : ℕ}
    (A : ConcreteGeneralizedAllowableSequence k r)
    (hpos : 0 < A.toCountedGeneralizedAllowableSequence.crossingMoves.card) where
  periodMoves : ℕ
  cyclic : ConcreteGeneralizedAllowableSequence k periodMoves
  lastCrossing : Fin periodMoves
  nextFirstCrossing : Fin periodMoves
  consecutive :
    cyclic.toCountedGeneralizedAllowableSequence.ConsecutiveCrossing
      lastCrossing nextFirstCrossing
  last_order :
    cyclic.toCountedGeneralizedAllowableSequence.moveOrder lastCrossing =
      A.toCountedGeneralizedAllowableSequence.moveOrder
        (A.toCountedGeneralizedAllowableSequence.crossingIdx
          ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by omega⟩)
  next_order :
    cyclic.toCountedGeneralizedAllowableSequence.moveOrder nextFirstCrossing =
      A.toCountedGeneralizedAllowableSequence.moveOrder
        (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, hpos⟩)
  cyclic_gap_eq :
    nextFirstCrossing.val - lastCrossing.val - 1 =
      (A.toCountedGeneralizedAllowableSequence.crossingIdx ⟨0, hpos⟩).val +
        (r - 1 -
          (A.toCountedGeneralizedAllowableSequence.crossingIdx
            ⟨A.toCountedGeneralizedAllowableSequence.crossingMoves.card - 1, by omega⟩).val)











end ConcreteGeneralizedAllowableSequence

































structure UngarLevelSweepCore (S : Finset Point2) (k : ℕ) where
  labeling : PointLabeling S k
  sequence : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card
  stepDir : Fin (directionsDeterminedBy S).card → Direction
  blocks_level : sequence.BlocksHaveCommonLevel labeling stepDir
  stepDir_injective : Function.Injective stepDir

structure UngarLevelSweepCertificate (S : Finset Point2) (k : ℕ) (hk : 0 < k) where
  labeling : PointLabeling S k
  sequence : ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy S).card
  stepDir : Fin (directionsDeterminedBy S).card → Direction
  blocks_level : sequence.BlocksHaveCommonLevel labeling stepDir
  stepDir_injective : Function.Injective stepDir
  cyclic_end_gap :
    sequence.CyclicEndGap
      (sequence.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)

namespace UngarLevelSweepCertificate











end UngarLevelSweepCertificate

namespace UngarLevelSweepCore







def toCertificate {S : Finset Point2} {k : ℕ}
    (C : UngarLevelSweepCore S k) (hk : 0 < k)
    (hend : C.sequence.CyclicEndGap
      (C.sequence.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)) :
    UngarLevelSweepCertificate S k hk where
  labeling := C.labeling
  sequence := C.sequence
  stepDir := C.stepDir
  blocks_level := C.blocks_level
  stepDir_injective := C.stepDir_injective
  cyclic_end_gap := hend

end UngarLevelSweepCore

abbrev EvenUngarLevelSweepCertificatePremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, S.card = 2 * k →
    NoncollinearSet S → Nonempty (UngarLevelSweepCertificate S k hk)

















































/-! ## Sweep certificate construction

The remaining geometric core: construct `UngarLevelSweepCertificate` from the
rotating projection sweep of every even non-collinear point set.
-/

/-! ### BlockMove from monotone level function -/

noncomputable def nontrivialLevelValues {N : ℕ} (g : Fin N → ℝ) : Finset ℝ :=
  (Finset.univ.image g).filter fun v =>
    (Finset.univ.filter fun i : Fin N => g i = v).card ≥ 2

noncomputable def nontrivialLevelRep {N : ℕ} (g : Fin N → ℝ) (v : ℝ)
    (hv : v ∈ nontrivialLevelValues g) : Fin N :=
  (Finset.univ.filter fun i : Fin N => g i = v).min' (by
    have hmem := (Finset.mem_filter.mp hv).2
    exact Finset.card_pos.mp (by omega))

theorem nontrivialLevelRep_val {N : ℕ} {g : Fin N → ℝ} {v : ℝ}
    (hv : v ∈ nontrivialLevelValues g) :
    g (nontrivialLevelRep g v hv) = v := by
  have hmem : nontrivialLevelRep g v hv ∈
      Finset.univ.filter (fun i : Fin N => g i = v) :=
    Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2

 theorem levelBlockLo_le_of_monotone_eq' {N : ℕ}
    {g : Fin N → ℝ} (_hg : Monotone g) {rep p : Fin N}
    (hval : g p = g rep) :
    levelBlockLo g rep ≤ p := by
  by_contra h
  push Not at h
  have hp_le_rep : p ≤ rep :=
    le_of_lt (lt_of_lt_of_le h levelBlockLo_le)
  have hp_in : p ∈ Finset.univ.filter fun j : Fin N => g j = g rep ∧ j ≤ rep :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval, hp_le_rep⟩
  exact not_le.mpr h (Finset.min'_le _ _ hp_in)

 theorem le_levelBlockHi_of_monotone_eq' {N : ℕ}
    {g : Fin N → ℝ} (_hg : Monotone g) {rep p : Fin N}
    (hval : g p = g rep) :
    p ≤ levelBlockHi g rep := by
  by_contra h
  push Not at h
  have hrep_le_p : rep ≤ p :=
    le_of_lt (lt_of_le_of_lt levelBlockHi_ge h)
  have hp_in : p ∈ Finset.univ.filter fun j : Fin N => g j = g rep ∧ rep ≤ j :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hval, hrep_le_p⟩
  exact not_le.mpr h (Finset.le_max' _ _ hp_in)

theorem nontrivialLevelRep_block {N : ℕ} {g : Fin N → ℝ} (hg : Monotone g) {v : ℝ}
    (hv : v ∈ nontrivialLevelValues g) :
    (levelBlockLo g (nontrivialLevelRep g v hv)).val <
      (levelBlockHi g (nontrivialLevelRep g v hv)).val := by
  by_contra h
  push Not at h
  have hle := Fin.le_def.mp (levelBlockLo_le (f := g) (i := nontrivialLevelRep g v hv))
  have hge := Fin.le_def.mp (levelBlockHi_ge (f := g) (i := nontrivialLevelRep g v hv))
  have hrep := nontrivialLevelRep_val hv
  have hsingleton : ∀ j : Fin N, g j = v → j = nontrivialLevelRep g v hv := by
    intro j hj
    have hj_ge := levelBlockLo_le_of_monotone_eq' hg (hj.trans hrep.symm)
    have hj_le := le_levelBlockHi_of_monotone_eq' hg (hj.trans hrep.symm)
    exact Fin.ext (by
      have := Fin.le_def.mp hj_ge
      have := Fin.le_def.mp hj_le
      omega)
  have : (Finset.univ.filter fun i : Fin N => g i = v).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    exact (hsingleton a (Finset.mem_filter.mp ha).2).trans
      (hsingleton b (Finset.mem_filter.mp hb).2).symm
  have := (Finset.mem_filter.mp hv).2
  omega

 theorem mem_levelBlockMoveInterval_of_same_value {N : ℕ}
    {g : Fin N → ℝ} (hg : Monotone g) {rep p : Fin N}
    (hrep_lo_lt : (levelBlockLo g rep).val < (levelBlockHi g rep).val)
    (hval : g p = g rep) :
    (levelBlockMoveInterval g rep hrep_lo_lt).Mem p :=
  ⟨Fin.le_def.mp (levelBlockLo_le_of_monotone_eq' hg hval),
   Fin.le_def.mp (le_levelBlockHi_of_monotone_eq' hg hval)⟩

 theorem levelBlockMirror_eq_mirror_of_mem_levelBlockMoveInterval {N : ℕ}
    {g : Fin N → ℝ} (hg : Monotone g) {rep p : Fin N}
    (hrep_lo_lt : (levelBlockLo g rep).val < (levelBlockHi g rep).val)
    (hp : (levelBlockMoveInterval g rep hrep_lo_lt).Mem p) :
    levelBlockMirror g p = (levelBlockMoveInterval g rep hrep_lo_lt).mirror p hp := by
  apply Fin.ext
  simp only [levelBlockMirror, PositionInterval.mirror, levelBlockMoveInterval]
  rcases hp with ⟨hlo, hhi⟩
  have hp_val := monotone_levelBlock_eq hg
    (Fin.le_def.mpr (show (levelBlockLo g rep).val ≤ p.val from hlo))
    (Fin.le_def.mpr (show p.val ≤ (levelBlockHi g rep).val from hhi))
  have hlo_eq := levelBlockLo_of_mem_block hp_val hlo
  have hhi_eq := levelBlockHi_of_mem_block hp_val hhi
  rw [← congrArg Fin.val hlo_eq, ← congrArg Fin.val hhi_eq]

 theorem levelBlockMirror_eq_self_of_singleton {N : ℕ}
    {g : Fin N → ℝ} (p : Fin N)
    (hsingleton : levelBlockLo g p = levelBlockHi g p) :
    levelBlockMirror g p = p := by
  apply Fin.ext
  simp [levelBlockMirror]
  have := congrArg Fin.val hsingleton
  have := Fin.le_def.mp (levelBlockLo_le (f := g) (i := p))
  have := Fin.le_def.mp (levelBlockHi_ge (f := g) (i := p))
  omega

 theorem mem_nontrivialLevelValues_of_nontrivial_block {N : ℕ}
    {g : Fin N → ℝ} {p : Fin N}
    (hlt : (levelBlockLo g p).val < (levelBlockHi g p).val) :
    g p ∈ nontrivialLevelValues g := by
  simp only [nontrivialLevelValues, Finset.mem_filter, Finset.mem_image]
  refine ⟨⟨p, Finset.mem_univ _, rfl⟩, ?_⟩
  have hlo_in : levelBlockLo g p ∈
      Finset.univ.filter fun i : Fin N => g i = g p :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, levelBlockLo_val⟩
  have hhi_in : levelBlockHi g p ∈
      Finset.univ.filter fun i : Fin N => g i = g p :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, levelBlockHi_val⟩
  exact Finset.one_lt_card.mpr ⟨levelBlockLo g p, hlo_in,
    levelBlockHi g p, hhi_in, fun h => absurd (congrArg Fin.val h) (by omega)⟩

noncomputable def levelBlockMoveBlock {N : ℕ} (g : Fin N → ℝ) (hg : Monotone g)
    (i : Fin (nontrivialLevelValues g).card) : PositionInterval N :=
  levelBlockMoveInterval g
    (nontrivialLevelRep g ((nontrivialLevelValues g).equivFin.symm i).val
      ((nontrivialLevelValues g).equivFin.symm i).property)
    (nontrivialLevelRep_block hg ((nontrivialLevelValues g).equivFin.symm i).property)

noncomputable def levelBlockMoveOfMonotone {N : ℕ} (g : Fin N → ℝ) (hg : Monotone g)
    (hnt : (nontrivialLevelValues g).Nonempty) : BlockMove N where
  blockCount := (nontrivialLevelValues g).card
  blockCount_pos := Finset.card_pos.mpr hnt
  block := levelBlockMoveBlock g hg
  pairwise_disjoint := by
    intro i _hi j _hj hij
    have hne : ((nontrivialLevelValues g).equivFin.symm i).val ≠
        ((nontrivialLevelValues g).equivFin.symm j).val := by
      intro h
      exact hij ((nontrivialLevelValues g).equivFin.symm.injective (Subtype.ext h))
    have hgne : g (nontrivialLevelRep g _ ((nontrivialLevelValues g).equivFin.symm i).property) ≠
        g (nontrivialLevelRep g _ ((nontrivialLevelValues g).equivFin.symm j).property) := by
      simp only [nontrivialLevelRep_val]; exact hne
    exact Set.disjoint_of_subset_left (le_refl _)
      (Set.disjoint_of_subset_right (le_refl _)
        (levelBlockMoveInterval_disjoint hg _ _ hgne))
  nontrivial := by
    intro i
    show 2 ≤ (levelBlockMoveBlock g hg i).length
    simp only [levelBlockMoveBlock, PositionInterval.length, levelBlockMoveInterval]
    have := nontrivialLevelRep_block hg ((nontrivialLevelValues g).equivFin.symm i).property
    omega
  map := levelBlockMirrorPerm g hg

theorem levelBlockMoveOfMonotone_reversesBlocks {N : ℕ} {g : Fin N → ℝ} {hg : Monotone g}
    {hnt : (nontrivialLevelValues g).Nonempty} :
    (levelBlockMoveOfMonotone g hg hnt).ReversesBlocks := by
  constructor
  · intro i p hp
    show (levelBlockMirrorPerm g hg) p = _
    simp only [levelBlockMirrorPerm]
    show levelBlockMirror g p = ((levelBlockMoveBlock g hg i).mirror p hp)
    exact levelBlockMirror_eq_mirror_of_mem_levelBlockMoveInterval hg _ hp
  · intro p hnot
    show (levelBlockMirrorPerm g hg) p = p
    simp only [levelBlockMirrorPerm]
    apply levelBlockMirror_eq_self_of_singleton
    by_contra hne
    have hlt : (levelBlockLo g p).val < (levelBlockHi g p).val := by
      have := Fin.le_def.mp (levelBlockLo_le (f := g) (i := p))
      have := Fin.le_def.mp (levelBlockHi_ge (f := g) (i := p))
      omega
    have hv_mem := mem_nontrivialLevelValues_of_nontrivial_block hlt
    let idx := (nontrivialLevelValues g).equivFin ⟨g p, hv_mem⟩
    have hval_eq : ((nontrivialLevelValues g).equivFin.symm idx).val = g p := by
      simp [idx]
    have hv' := ((nontrivialLevelValues g).equivFin.symm idx).property
    have hrep_val : g (nontrivialLevelRep g
        ((nontrivialLevelValues g).equivFin.symm idx).val hv') = g p := by
      rw [nontrivialLevelRep_val hv', hval_eq]
    exact absurd (mem_levelBlockMoveInterval_of_same_value hg
      (nontrivialLevelRep_block hg hv') hrep_val.symm) (hnot idx)

/-! ### ReversalStep from sweep event -/

 theorem same_g_value_of_same_block {N : ℕ} {g : Fin N → ℝ}
    (hg : Monotone g) {hnt : (nontrivialLevelValues g).Nonempty}
    {i : Fin (levelBlockMoveOfMonotone g hg hnt).blockCount}
    {p q : Fin N}
    (hp : ((levelBlockMoveOfMonotone g hg hnt).block i).Mem p)
    (hq : ((levelBlockMoveOfMonotone g hg hnt).block i).Mem q) :
    g p = g q := by
  have hrep_block := nontrivialLevelRep_block hg
    ((nontrivialLevelValues g).equivFin.symm i).property
  have hp_val := monotone_levelBlock_eq hg (Fin.le_def.mpr hp.1) (Fin.le_def.mpr hp.2)
  have hq_val := monotone_levelBlock_eq hg (Fin.le_def.mpr hq.1) (Fin.le_def.mpr hq.2)
  exact hp_val.trans hq_val.symm

noncomputable def sweepReversalStep {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    {θ₁ θ_e θ₂ θ₀ : ℝ}
    (_hinj₀ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₀ (L.point a)))
    (hinj₁ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₁ (L.point a)))
    (hinj₂ : Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₂ (L.point a)))
    (hid : sweepSort L θ₀ = Equiv.refl _)
    (h1e : θ₁ < θ_e) (he2 : θ_e < θ₂) (h_span : θ₂ - θ₁ < Real.pi)
    (honly_event : ∀ a b : Fin (2 * k), L.point a ≠ L.point b →
      ∀ θ ∈ Set.Icc θ₁ θ₂, θ ≠ θ_e →
        orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b))
    (hno_tie_0_to_1 : ∀ a b : Fin (2 * k), L.point a ≠ L.point b →
      orientedLevel θ_e (L.point a) = orientedLevel θ_e (L.point b) →
        ∀ θ ∈ Set.Icc θ₀ θ₁, orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b))
    (h01 : θ₀ ≤ θ₁)
    (hg_mono : Monotone (fun i => orientedLevel θ_e
      (L.point (sweepSort L θ₁ i))))
    (hnt : (nontrivialLevelValues (fun i => orientedLevel θ_e
      (L.point (sweepSort L θ₁ i)))).Nonempty) :
    ReversalStep k (sweepSort L θ₁) (sweepSort L θ₂) where
  move := levelBlockMoveOfMonotone
    (fun i => orientedLevel θ_e (L.point (sweepSort L θ₁ i))) hg_mono hnt
  step_apply := by
    intro p
    have hcomp := sweepSort_event_compose L hinj₁ hinj₂ h1e he2 h_span honly_event hg_mono
    show (sweepSort L θ₂) p = (sweepSort L θ₁)
      ((levelBlockMoveOfMonotone _ hg_mono hnt).map p)
    simp only [levelBlockMoveOfMonotone]
    rw [hcomp]; rfl
  increasing_before := by
    set g := fun i => orientedLevel θ_e (L.point (sweepSort L θ₁ i))
    intro i p hp q hq hpq
    simp only [PositionInterval.toSet, Set.mem_setOf_eq] at hp hq
    have htie : orientedLevel θ_e (L.point (sweepSort L θ₁ p)) =
        orientedLevel θ_e (L.point (sweepSort L θ₁ q)) :=
      same_g_value_of_same_block hg_mono hp hq
    have hstrict := sweepSort_strictMono_of_injective L θ₁ hinj₁ hpq
    have hne : L.point (sweepSort L θ₁ p) ≠ L.point (sweepSort L θ₁ q) :=
      fun h => ne_of_lt hstrict (congr_arg (orientedLevel θ₁) h)
    have hord₀ := orientedLevel_order_preserved_backward h01 hstrict
      (fun θ hθ => hno_tie_0_to_1 _ _ hne htie θ hθ)
    exact label_index_lt_of_orientedLevel_lt L θ₀ hid hord₀

/-! ### Sorted direction angle infrastructure -/

theorem sortedDirectionAngles_length (points : Finset Point2) :
    (sortedDirectionAngles points).length =
      (directionsDeterminedBy points).card := by
  simp [sortedDirectionAngles, Finset.card_image_of_injective _ Direction.angle_injective]

theorem sortedDirectionAngles_sortedLT (points : Finset Point2) :
    (sortedDirectionAngles points).SortedLT :=
  Finset.sortedLT_sort _



noncomputable def sortedAngleAt (points : Finset Point2)
    (j : Fin (directionsDeterminedBy points).card) : ℝ :=
  (sortedDirectionAngles points).get ⟨j.val, by
    have := sortedDirectionAngles_length points; omega⟩

theorem sortedAngleAt_strictMono (points : Finset Point2) :
    StrictMono (sortedAngleAt points) := by
  intro i j hij
  have hsorted := sortedDirectionAngles_sortedLT points
  show (sortedDirectionAngles points).get ⟨i.val, _⟩ <
    (sortedDirectionAngles points).get ⟨j.val, _⟩
  exact hsorted.strictMono_get hij

theorem sortedAngleAt_mem (points : Finset Point2)
    (j : Fin (directionsDeterminedBy points).card) :
    sortedAngleAt points j ∈
      (directionsDeterminedBy points).image Direction.angle := by
  have hmem : sortedAngleAt points j ∈ sortedDirectionAngles points :=
    List.get_mem _ _
  rwa [sortedDirectionAngles, Finset.mem_sort] at hmem

theorem sortedAngleAt_nonneg (points : Finset Point2)
    (j : Fin (directionsDeterminedBy points).card) :
    0 ≤ sortedAngleAt points j := by
  rcases Finset.mem_image.mp (sortedAngleAt_mem points j) with ⟨d, _, hangle⟩
  rw [← hangle]; exact d.angle_nonneg

theorem sortedAngleAt_lt_pi (points : Finset Point2)
    (j : Fin (directionsDeterminedBy points).card) :
    sortedAngleAt points j < Real.pi := by
  rcases Finset.mem_image.mp (sortedAngleAt_mem points j) with ⟨d, _, hangle⟩
  rw [← hangle]; exact d.angle_lt_pi

theorem orientedLevel_eq_at_direction_angle {p q : Point2} (_hpq : p ≠ q) :
    orientedLevel (direction p q).angle p = orientedLevel (direction p q).angle q := by
  cases hd : direction p q with
  | vertical =>
    simp only [Direction.angle]
    simp [orientedLevel, Real.sin_pi_div_two, Real.cos_pi_div_two]
    have : p.1 = q.1 := by unfold direction at hd; split_ifs at hd with hx; exact hx
    linarith
  | finite m =>
    have hcos_ne : Real.cos (Direction.finite m).angle ≠ 0 := by
      simp only [Direction.angle]
      split_ifs with h
      · exact ne_of_gt (Real.cos_arctan_pos m)
      · rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
        simp; exact ne_of_lt (Real.cos_arctan_pos m) |>.symm
    have htan_eq : Direction.finite (Real.tan (Direction.finite m).angle) =
        Direction.finite m := by
      congr 1; simp only [Direction.angle]
      split_ifs with h
      · exact Real.tan_arctan m
      · rw [Real.tan_add_pi]; exact Real.tan_arctan m
    rw [orientedLevel_eq_cos_mul_directionLevel hcos_ne,
        orientedLevel_eq_cos_mul_directionLevel hcos_ne, htan_eq]
    exact congrArg _ (directionLevel_eq_of_direction_eq hd)

 theorem orientedLevel_sub_zero_at_direction_angle' {p q : Point2} (hpq : p ≠ q) :
    -(p.1 - q.1) * Real.sin (direction p q).angle +
      (p.2 - q.2) * Real.cos (direction p q).angle = 0 := by
  have h := orientedLevel_sub_eq (direction p q).angle p q
  linarith [orientedLevel_eq_at_direction_angle hpq]

theorem orientedLevel_ne_of_angle_between {p q : Point2} (hpq : p ≠ q)
    {θ₀ : ℝ}
    (hlo : (direction p q).angle - Real.pi < θ₀)
    (hhi : θ₀ < (direction p q).angle) :
    orientedLevel θ₀ p ≠ orientedLevel θ₀ q := by
  intro htie
  have hzero_d := orientedLevel_sub_zero_at_direction_angle' hpq
  have hprod := sinusoid_product_formula hzero_d (θ₁ := θ₀) (θ₂ := θ₀)
  have hzero₀ : -(p.1 - q.1) * Real.sin θ₀ + (p.2 - q.2) * Real.cos θ₀ = 0 := by
    have := orientedLevel_sub_eq θ₀ p q; linarith
  have hsin_neg : Real.sin (θ₀ - (direction p q).angle) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  have hpq_ne : -(p.1 - q.1) ≠ 0 ∨ (p.2 - q.2) ≠ 0 := by
    by_contra h; push Not at h
    exact hpq (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
  have h_sq_pos : 0 < (-(p.1 - q.1)) ^ 2 + (p.2 - q.2) ^ 2 := by
    rcases hpq_ne with ha | hb <;> positivity
  have hsin_sq_pos : 0 < Real.sin (θ₀ - (direction p q).angle) *
      Real.sin (θ₀ - (direction p q).angle) :=
    mul_pos_of_neg_of_neg hsin_neg hsin_neg
  have h_rhs_pos : 0 < ((-(p.1 - q.1)) ^ 2 + (p.2 - q.2) ^ 2) *
      (Real.sin (θ₀ - (direction p q).angle) * Real.sin (θ₀ - (direction p q).angle)) :=
    mul_pos h_sq_pos hsin_sq_pos
  have h_lhs_zero : (-(p.1 - q.1) * Real.sin θ₀ + (p.2 - q.2) * Real.cos θ₀) *
      (-(p.1 - q.1) * Real.sin θ₀ + (p.2 - q.2) * Real.cos θ₀) = 0 := by
    rw [hzero₀]; ring
  nlinarith [hprod, h_lhs_zero, h_rhs_pos]

theorem orientedLevel_injective_of_all_angles_between {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    {θ₀ : ℝ}
    (hlo : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hhi : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle) :
    Function.Injective (fun a : Fin (2 * k) => orientedLevel θ₀ (L.point a)) := by
  intro a b hab
  by_contra hne
  have hab' : a ≠ b := fun h => by subst h; exact hne rfl
  have hpq : L.point a ≠ L.point b := fun h => hab' (L.point_injective h)
  have hdir_mem := L.direction_mem hab'
  exact orientedLevel_ne_of_angle_between hpq (hlo _ hdir_mem) (hhi _ hdir_mem) hab

theorem orientedLevel_injective_at_non_direction_angle {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k) {θ : ℝ}
    (hθ₁ : 0 ≤ θ) (hθ₂ : θ < Real.pi)
    (hne : ∀ d ∈ directionsDeterminedBy points, d.angle ≠ θ) :
    Function.Injective (fun a : Fin (2 * k) => orientedLevel θ (L.point a)) := by
  intro a b hab
  by_contra hneq
  have hab' : a ≠ b := fun h => by subst h; exact hneq rfl
  have hpq : L.point a ≠ L.point b := fun h => hab' (L.point_injective h)
  have hdir_mem := L.direction_mem hab'
  have hdir_angle : (direction (L.point a) (L.point b)).angle = θ :=
    orientedLevel_unique_tie_angle hpq (Direction.angle_nonneg _) (Direction.angle_lt_pi _)
      hθ₁ hθ₂ (orientedLevel_eq_at_direction_angle hpq) hab
  exact hne _ hdir_mem hdir_angle

/-! ### Starting angle selection -/

noncomputable def sweepStartAngle (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty) : ℝ :=
  let angles := (directionsDeterminedBy points).image Direction.angle
  let minA := angles.min' (Finset.Nonempty.image hne _)
  let maxA := angles.max' (Finset.Nonempty.image hne _)
  (maxA - Real.pi + minA) / 2

 theorem angles_max_lt_pi (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty) :
    ((directionsDeterminedBy points).image Direction.angle).max'
      (Finset.Nonempty.image hne _) < Real.pi := by
  rcases Finset.mem_image.mp (Finset.max'_mem _
    (Finset.Nonempty.image hne Direction.angle)) with ⟨d', _, h⟩
  linarith [d'.angle_lt_pi]

 theorem angles_min_nonneg (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty) :
    0 ≤ ((directionsDeterminedBy points).image Direction.angle).min'
      (Finset.Nonempty.image hne _) := by
  rcases Finset.mem_image.mp (Finset.min'_mem _
    (Finset.Nonempty.image hne Direction.angle)) with ⟨d', _, h⟩
  linarith [d'.angle_nonneg]

theorem sweepStartAngle_lt_min (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (d : Direction) (hd : d ∈ directionsDeterminedBy points) :
    sweepStartAngle points hne < d.angle := by
  simp only [sweepStartAngle]
  have hmin := Finset.min'_le _ d.angle (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
  linarith [angles_max_lt_pi points hne, angles_min_nonneg points hne]

theorem sweepStartAngle_gt_max_sub_pi (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (d : Direction) (hd : d ∈ directionsDeterminedBy points) :
    d.angle - Real.pi < sweepStartAngle points hne := by
  simp only [sweepStartAngle]
  have hmax := Finset.le_max' _ d.angle (Finset.mem_image.mpr ⟨d, hd, rfl⟩)
  linarith [angles_max_lt_pi points hne, angles_min_nonneg points hne]

/-! ### Inter-event angles -/

noncomputable def interEventAngle (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin ((directionsDeterminedBy points).card + 1)) : ℝ :=
  let θ₀ := sweepStartAngle points hne
  if hj0 : j.val = 0 then θ₀
  else if hjr : j.val = (directionsDeterminedBy points).card then θ₀ + Real.pi
  else
    let j_pred : Fin (directionsDeterminedBy points).card :=
      ⟨j.val - 1, by omega⟩
    let j_curr : Fin (directionsDeterminedBy points).card :=
      ⟨j.val, by omega⟩
    genericAngleBetween (sortedAngleAt points j_pred) (sortedAngleAt points j_curr)

theorem interEventAngle_zero (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty) :
    interEventAngle points hne ⟨0, Nat.succ_pos _⟩ = sweepStartAngle points hne := by
  simp [interEventAngle]

theorem interEventAngle_last (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty) :
    interEventAngle points hne ⟨(directionsDeterminedBy points).card,
      Nat.lt_succ_self _⟩ = sweepStartAngle points hne + Real.pi := by
  simp only [interEventAngle]
  have : ¬ (directionsDeterminedBy points).card = 0 :=
    Finset.card_ne_zero.mpr hne
  simp [this]

/-! ### No-tie conditions between inter-event angles -/

theorem direction_angle_eq_sortedAngleAt {points : Finset Point2}
    (d : Direction) (hd : d ∈ directionsDeterminedBy points) :
    ∃ j : Fin (directionsDeterminedBy points).card,
      d.angle = sortedAngleAt points j := by
  have hmem := (sortedDirectionAngles_sortedLT points).strictMono_get
  have hd_mem : d.angle ∈ sortedDirectionAngles points := by
    rw [sortedDirectionAngles, Finset.mem_sort]
    exact Finset.mem_image.mpr ⟨d, hd, rfl⟩
  rcases List.mem_iff_get.mp hd_mem with ⟨⟨i, hi_lt⟩, hi⟩
  have hi_len : i < (directionsDeterminedBy points).card := by
    rwa [← sortedDirectionAngles_length]
  refine ⟨⟨i, hi_len⟩, ?_⟩
  show d.angle = sortedAngleAt points ⟨i, hi_len⟩
  unfold sortedAngleAt
  show d.angle = (sortedDirectionAngles points).get ⟨i, _⟩
  exact hi.symm







/-! ### Sweep labeling and GAS -/

noncomputable def sweepLabeling {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty) :
    PointLabeling points k :=
  (PointLabeling.ofCard hcard).reindex (sweepSort (PointLabeling.ofCard hcard)
    (sweepStartAngle points hne))

theorem sweepLabeling_id {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty) :
    sweepSort (sweepLabeling hcard hne) (sweepStartAngle points hne) = Equiv.refl _ :=
  sweepSort_reindex_eq_refl _ _

theorem sweepLabeling_inj {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty) :
    Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel (sweepStartAngle points hne) ((sweepLabeling hcard hne).point a)) :=
  orientedLevel_injective_of_all_angles_between _
    (fun d hd => sweepStartAngle_gt_max_sub_pi points hne d hd)
    (fun d hd => sweepStartAngle_lt_min points hne d hd)

noncomputable def sweepGAS {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (_hncoll : NoncollinearSet points) :
    GeneralizedAllowableSequence k (directionsDeterminedBy points).card :=
  GeneralizedAllowableSequence.ofSweepAngles (sweepLabeling hcard hne)
    (interEventAngle points hne)
    (by rw [interEventAngle_zero]; exact sweepLabeling_id hcard hne)
    (by rw [interEventAngle_last, interEventAngle_zero])
    (by rw [interEventAngle_zero]; exact sweepLabeling_inj hcard hne)



/-! ### Inter-event angle ordering -/

theorem interEventAngle_lt_sortedAngle {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin (directionsDeterminedBy points).card) :
    interEventAngle points hne ⟨j.val, by omega⟩ < sortedAngleAt points j := by
  rcases Finset.mem_image.mp (sortedAngleAt_mem points j) with ⟨d, hd, hangle⟩
  unfold interEventAngle
  by_cases hj0 : j.val = 0
  · simp [hj0, ← hangle]; exact sweepStartAngle_lt_min points hne d hd
  · have : ¬(j.val = (directionsDeterminedBy points).card) := by
      have := j.isLt; omega
    simp [hj0, this]
    exact genericAngleBetween_lt' (sortedAngleAt_strictMono points
      (show (⟨j.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩ : Fin _) < j from
        Fin.lt_def.mpr (Nat.sub_one_lt_of_le (Nat.pos_of_ne_zero hj0) (le_refl _))))

theorem sortedAngle_lt_interEventAngle_succ {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin (directionsDeterminedBy points).card) :
    sortedAngleAt points j < interEventAngle points hne ⟨j.val + 1, by omega⟩ := by
  rcases Finset.mem_image.mp (sortedAngleAt_mem points j) with ⟨d, hd, hangle⟩
  unfold interEventAngle
  have hne0 : ¬(j.val + 1 = 0) := by omega
  by_cases hjr : j.val + 1 = (directionsDeterminedBy points).card
  · show sortedAngleAt points j < interEventAngle points hne ⟨j.val + 1, by omega⟩
    calc sortedAngleAt points j = d.angle := hangle.symm
      _ < sweepStartAngle points hne + Real.pi := by
            linarith [sweepStartAngle_gt_max_sub_pi points hne d hd]
      _ = interEventAngle points hne ⟨(directionsDeterminedBy points).card,
            Nat.lt_succ_self _⟩ := (interEventAngle_last points hne).symm
      _ = interEventAngle points hne ⟨j.val + 1, by omega⟩ := by
            congr 1; exact Fin.ext hjr.symm
  · have hjr' : j.val + 1 < (directionsDeterminedBy points).card := by
      cases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt j.isLt) with
      | inl h => exact h
      | inr h => exact absurd h hjr
    simp only [hne0, hjr, ↓reduceDIte]
    exact genericAngleBetween_lt (sortedAngleAt_strictMono points
      (show j < (⟨j.val + 1, hjr'⟩ : Fin _) from
        Fin.lt_def.mpr (Nat.lt_succ_self _)))

/-! ### Span and bounds for inter-event angles -/

theorem interEventAngle_le_start_add_pi {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin ((directionsDeterminedBy points).card + 1)) :
    interEventAngle points hne j ≤ sweepStartAngle points hne + Real.pi := by
  rcases eq_or_ne j.val (directionsDeterminedBy points).card with hjr | hjr
  · rw [show j = ⟨_, Nat.lt_succ_self _⟩ from Fin.ext hjr, interEventAngle_last]
  · have hj_lt : j.val < (directionsDeterminedBy points).card := by
      have := j.isLt; omega
    have h := interEventAngle_lt_sortedAngle hne ⟨j.val, hj_lt⟩
    rcases Finset.mem_image.mp (sortedAngleAt_mem points ⟨j.val, hj_lt⟩) with ⟨d, hd, hangle⟩
    have : (⟨j.val, (by omega : j.val < _ + 1)⟩ : Fin _) = j := Fin.ext rfl
    rw [this] at h
    linarith [sweepStartAngle_gt_max_sub_pi points hne d hd,
              sortedAngleAt_lt_pi points ⟨j.val, hj_lt⟩]

theorem sweepStartAngle_le_interEventAngle {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin ((directionsDeterminedBy points).card + 1)) :
    sweepStartAngle points hne ≤ interEventAngle points hne j := by
  rcases eq_or_ne j.val 0 with hj0 | hj0
  · rw [show j = ⟨0, Nat.succ_pos _⟩ from Fin.ext hj0, interEventAngle_zero]
  · rcases eq_or_ne j.val (directionsDeterminedBy points).card with hjr | hjr
    · rw [show j = ⟨_, Nat.lt_succ_self _⟩ from Fin.ext hjr, interEventAngle_last]
      linarith [Real.pi_pos]
    · have hj_pos := Nat.pos_of_ne_zero hj0
      have hj_lt : j.val < (directionsDeterminedBy points).card := by
        have := j.isLt; omega
      have hj_pred_lt : j.val - 1 < (directionsDeterminedBy points).card := by omega
      rcases Finset.mem_image.mp (sortedAngleAt_mem points
        ⟨j.val - 1, hj_pred_lt⟩) with ⟨d, hd, hangle⟩
      have hprev := sortedAngle_lt_interEventAngle_succ hne ⟨j.val - 1, hj_pred_lt⟩
      have hfin_eq : (⟨(⟨j.val - 1, hj_pred_lt⟩ : Fin _).val + 1,
          (by have := j.isLt; have := hj_pos; omega :
            (⟨j.val - 1, hj_pred_lt⟩ : Fin _).val + 1 <
              (directionsDeterminedBy points).card + 1)⟩ :
          Fin ((directionsDeterminedBy points).card + 1)) = j :=
        Fin.ext (Nat.succ_pred_eq_of_pos hj_pos)
      rw [hfin_eq] at hprev
      linarith [sweepStartAngle_lt_min points hne d hd]

theorem interEventAngle_span {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (j : Fin (directionsDeterminedBy points).card) :
    interEventAngle points hne ⟨j.val + 1, by omega⟩ -
      interEventAngle points hne ⟨j.val, by omega⟩ < Real.pi := by
  have h1 := interEventAngle_lt_sortedAngle hne j
  have h2 := sortedAngle_lt_interEventAngle_succ hne j
  have hhi := sortedAngleAt_lt_pi points j
  have hlo := sortedAngleAt_nonneg points j
  have htop := interEventAngle_le_start_add_pi hne ⟨j.val + 1, by omega⟩
  have hbot := sweepStartAngle_le_interEventAngle hne ⟨j.val, by omega⟩
  have htop := interEventAngle_le_start_add_pi hne ⟨j.val + 1, by omega⟩
  have hbot := sweepStartAngle_le_interEventAngle hne ⟨j.val, by omega⟩
  by_cases hj0 : j.val = 0
  · have hj_succ_lt : j.val + 1 < (directionsDeterminedBy points).card := by omega
    have htop_strict : interEventAngle points hne ⟨j.val + 1, by omega⟩ <
        sweepStartAngle points hne + Real.pi := by
      have hlt := interEventAngle_lt_sortedAngle hne ⟨j.val + 1, hj_succ_lt⟩
      rcases Finset.mem_image.mp (sortedAngleAt_mem points
        ⟨j.val + 1, hj_succ_lt⟩) with ⟨d', hd', ha'⟩
      linarith [sweepStartAngle_gt_max_sub_pi points hne d' hd',
                sortedAngleAt_lt_pi points ⟨j.val + 1, hj_succ_lt⟩]
    have hbot_eq : interEventAngle points hne ⟨j.val, by omega⟩ =
        sweepStartAngle points hne := by
      rw [show (⟨j.val, (by omega : j.val < _ + 1)⟩ : Fin _) =
        ⟨0, Nat.succ_pos _⟩ from Fin.ext hj0, interEventAngle_zero]
    linarith
  · have hbot_strict : sweepStartAngle points hne <
        interEventAngle points hne ⟨j.val, by omega⟩ := by
      have hj_pos := Nat.pos_of_ne_zero hj0
      rcases Finset.mem_image.mp (sortedAngleAt_mem points
        ⟨j.val - 1, by have := j.isLt; omega⟩) with ⟨d', hd', ha'⟩
      have hprev := sortedAngle_lt_interEventAngle_succ hne
        ⟨j.val - 1, by have := j.isLt; omega⟩
      have hval_eq : (⟨j.val - 1, (by have := j.isLt; omega)⟩ :
          Fin (directionsDeterminedBy points).card).val + 1 = j.val :=
        Nat.succ_pred_eq_of_pos hj_pos
      have hfin_eq : (⟨(⟨j.val - 1, (by have := j.isLt; omega)⟩ :
          Fin (directionsDeterminedBy points).card).val + 1,
          (hval_eq ▸ (show j.val < (directionsDeterminedBy points).card + 1 from
            by have := j.isLt; omega))⟩ :
          Fin ((directionsDeterminedBy points).card + 1)) =
          ⟨j.val, by have := j.isLt; omega⟩ :=
        Fin.ext hval_eq
      rw [hfin_eq] at hprev
      linarith [sweepStartAngle_lt_min points hne d' hd']
    linarith

/-! ### Generalized non-tie and only-event condition -/

theorem orientedLevel_ne_of_ne_mod_pi {p q : Point2} (hpq : p ≠ q)
    {θ : ℝ}
    (hlo : (direction p q).angle - Real.pi < θ)
    (hhi : θ < (direction p q).angle + Real.pi)
    (hne : θ ≠ (direction p q).angle) :
    orientedLevel θ p ≠ orientedLevel θ q := by
  intro htie
  have hzero_d := orientedLevel_sub_zero_at_direction_angle' hpq
  have hprod := sinusoid_product_formula hzero_d (θ₁ := θ) (θ₂ := θ)
  have hzero₀ : -(p.1 - q.1) * Real.sin θ + (p.2 - q.2) * Real.cos θ = 0 := by
    have := orientedLevel_sub_eq θ p q; linarith
  have hpq_ne : -(p.1 - q.1) ≠ 0 ∨ (p.2 - q.2) ≠ 0 := by
    by_contra h; push Not at h
    exact hpq (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
  have h_sq_pos : 0 < (-(p.1 - q.1)) ^ 2 + (p.2 - q.2) ^ 2 := by
    rcases hpq_ne with ha | hb <;> positivity
  have hsin_ne : Real.sin (θ - (direction p q).angle) ≠ 0 := by
    intro hsin
    rw [Real.sin_eq_zero_iff] at hsin
    rcases hsin with ⟨n, hn⟩
    have hbound : |θ - (direction p q).angle| < Real.pi := by
      rw [abs_lt]; constructor <;> linarith
    have : n = 0 := by
      by_contra hn0
      have := Int.one_le_abs hn0
      have : Real.pi ≤ |↑n * Real.pi| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        exact le_mul_of_one_le_left (le_of_lt Real.pi_pos) (by exact_mod_cast this)
      linarith [show |↑n * Real.pi| = |θ - (direction p q).angle| from by rw [hn]]
    simp [this] at hn; exact hne (by linarith)
  have hsin_sq_pos : 0 < Real.sin (θ - (direction p q).angle) *
      Real.sin (θ - (direction p q).angle) :=
    mul_self_pos.mpr hsin_ne
  have h_lhs_zero : (-(p.1 - q.1) * Real.sin θ + (p.2 - q.2) * Real.cos θ) *
      (-(p.1 - q.1) * Real.sin θ + (p.2 - q.2) * Real.cos θ) = 0 := by
    rw [hzero₀]; ring
  nlinarith [hprod, h_lhs_zero, mul_pos h_sq_pos hsin_sq_pos]

theorem orientedLevel_ne_of_ne_tie_angle_in_pi_window {p q : Point2} (hpq : p ≠ q)
    {θ δ : ℝ}
    (htieδ : orientedLevel δ p = orientedLevel δ q)
    (hlo : δ - Real.pi < θ)
    (hhi : θ < δ + Real.pi)
    (hne : θ ≠ δ) :
    orientedLevel θ p ≠ orientedLevel θ q := by
  intro htie
  have hzeroδ : -(p.1 - q.1) * Real.sin δ + (p.2 - q.2) * Real.cos δ = 0 := by
    have := orientedLevel_sub_eq δ p q; linarith
  have hprod := sinusoid_product_formula hzeroδ (θ₁ := θ) (θ₂ := θ)
  have hzeroθ : -(p.1 - q.1) * Real.sin θ + (p.2 - q.2) * Real.cos θ = 0 := by
    have := orientedLevel_sub_eq θ p q; linarith
  have hpq_ne : -(p.1 - q.1) ≠ 0 ∨ (p.2 - q.2) ≠ 0 := by
    by_contra h; push Not at h
    exact hpq (Prod.ext (by linarith [h.1]) (by linarith [h.2]))
  have h_sq_pos : 0 < (-(p.1 - q.1)) ^ 2 + (p.2 - q.2) ^ 2 := by
    rcases hpq_ne with ha | hb <;> positivity
  have hsin_ne : Real.sin (θ - δ) ≠ 0 := by
    intro hsin
    rw [Real.sin_eq_zero_iff] at hsin
    rcases hsin with ⟨n, hn⟩
    have hbound : |θ - δ| < Real.pi := by
      rw [abs_lt]; constructor <;> linarith
    have : n = 0 := by
      by_contra hn0
      have := Int.one_le_abs hn0
      have : Real.pi ≤ |↑n * Real.pi| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
        exact le_mul_of_one_le_left (le_of_lt Real.pi_pos) (by exact_mod_cast this)
      linarith [show |↑n * Real.pi| = |θ - δ| from by rw [hn]]
    simp [this] at hn
    exact hne (by linarith)
  have hsin_sq_pos : 0 < Real.sin (θ - δ) * Real.sin (θ - δ) :=
    mul_self_pos.mpr hsin_ne
  have h_lhs_zero : (-(p.1 - q.1) * Real.sin θ + (p.2 - q.2) * Real.cos θ) *
      (-(p.1 - q.1) * Real.sin θ + (p.2 - q.2) * Real.cos θ) = 0 := by
    rw [hzeroθ]; ring
  nlinarith [hprod, h_lhs_zero, mul_pos h_sq_pos hsin_sq_pos]

theorem orientedLevel_injective_of_all_angles_mod_pi {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    {θ : ℝ}
    (hlo : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ)
    (hhi : ∀ d ∈ directionsDeterminedBy points, θ < d.angle + Real.pi)
    (hne : ∀ d ∈ directionsDeterminedBy points, θ ≠ d.angle) :
    Function.Injective (fun a : Fin (2 * k) => orientedLevel θ (L.point a)) := by
  intro a b hab
  by_contra hneq
  have hab' : a ≠ b := fun h => by subst h; exact hneq rfl
  have hpq : L.point a ≠ L.point b := fun h => hab' (L.point_injective h)
  have hdir_mem := L.direction_mem hab'
  exact orientedLevel_ne_of_ne_mod_pi hpq
    (hlo _ hdir_mem) (hhi _ hdir_mem) (hne _ hdir_mem) hab

theorem only_event_between_interEventAngles {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin (directionsDeterminedBy points).card)
    (a b : Fin (2 * k)) (hab : L.point a ≠ L.point b)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (interEventAngle points hne ⟨j.val, by omega⟩)
      (interEventAngle points hne ⟨j.val + 1, by omega⟩))
    (hθ_ne : θ ≠ sortedAngleAt points j) :
    orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b) := by
  have hab' : a ≠ b := fun h => hab (congr_arg L.point h)
  have hdir_mem := L.direction_mem hab'
  rcases direction_angle_eq_sortedAngleAt _ hdir_mem with ⟨idx, hangle_eq⟩
  rcases Finset.mem_image.mp (sortedAngleAt_mem points idx) with ⟨d_idx, hd_idx, ha_idx⟩
  have hθ_ne_dir : θ ≠ (direction (L.point a) (L.point b)).angle := by
    intro heq; rw [hangle_eq] at heq
    rcases eq_or_ne idx j with hidx | hidx
    · rw [hidx] at heq; exact hθ_ne heq
    · rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hidx) with h | h
      · have hj_pos : 0 < j.val := by omega
        have hj_pred_lt : j.val - 1 < (directionsDeterminedBy points).card :=
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
        have := (sortedAngleAt_strictMono points).monotone
          (show idx ≤ ⟨j.val - 1, hj_pred_lt⟩ from
            Fin.le_def.mpr (Nat.le_sub_one_of_lt h))
        have hprev := sortedAngle_lt_interEventAngle_succ hne ⟨j.val - 1, hj_pred_lt⟩
        have hval_eq : (⟨j.val - 1, hj_pred_lt⟩ : Fin _).val + 1 = j.val :=
          Nat.succ_pred_eq_of_pos hj_pos
        have hfin_eq : (⟨(⟨j.val - 1, hj_pred_lt⟩ :
            Fin (directionsDeterminedBy points).card).val + 1,
            lt_of_eq_of_lt hval_eq (Nat.lt_succ_of_lt j.isLt)⟩ :
            Fin ((directionsDeterminedBy points).card + 1)) =
            ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ :=
          Fin.ext hval_eq
        rw [hfin_eq] at hprev
        linarith [heq, hθ.1, hprev, this]
      · have hj1 : j.val + 1 < (directionsDeterminedBy points).card := by
          have := idx.isLt; omega
        have := (sortedAngleAt_strictMono points).monotone
          (show (⟨j.val + 1, hj1⟩ : Fin _) ≤ idx from
            Fin.le_def.mpr (Nat.succ_le_of_lt h))
        linarith [interEventAngle_lt_sortedAngle hne ⟨j.val + 1, hj1⟩,
                  sortedAngle_lt_interEventAngle_succ hne j, hθ.2]
  exact orientedLevel_ne_of_ne_mod_pi hab
    (by linarith [sweepStartAngle_le_interEventAngle hne ⟨j.val, by omega⟩,
                  sweepStartAngle_gt_max_sub_pi points hne _ hdir_mem, hθ.1])
    (by linarith [interEventAngle_le_start_add_pi hne ⟨j.val + 1, by omega⟩,
                  sweepStartAngle_lt_min points hne _ hdir_mem, hθ.2])
    hθ_ne_dir

/-! ### No-tie from θ₀ to inter-event angle -/

theorem no_tie_from_start_to_interEvent {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin (directionsDeterminedBy points).card)
    (a b : Fin (2 * k)) (hab : L.point a ≠ L.point b)
    (htie : orientedLevel (sortedAngleAt points j) (L.point a) =
      orientedLevel (sortedAngleAt points j) (L.point b))
    {θ : ℝ} (hθ : θ ∈ Set.Icc (sweepStartAngle points hne)
      (interEventAngle points hne ⟨j.val, by omega⟩)) :
    orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b) := by
  have hab' : a ≠ b := fun h => hab (congr_arg L.point h)
  have hdir_mem := L.direction_mem hab'
  apply orientedLevel_ne_of_ne_mod_pi hab
  · linarith [sweepStartAngle_gt_max_sub_pi points hne _ hdir_mem, hθ.1]
  · linarith [sweepStartAngle_lt_min points hne _ hdir_mem,
              interEventAngle_le_start_add_pi hne ⟨j.val, by omega⟩, hθ.2]
  · rcases direction_angle_eq_sortedAngleAt _ hdir_mem with ⟨idx, hangle_eq⟩
    have htie_at_idx := orientedLevel_eq_at_direction_angle hab
    rw [show (direction (L.point a) (L.point b)).angle = sortedAngleAt points idx from
      hangle_eq] at htie_at_idx
    have hidx_eq_j : idx = j := by
      by_contra hne_idx
      exact absurd (orientedLevel_unique_tie_angle hab
        (sortedAngleAt_nonneg _ _) (sortedAngleAt_lt_pi _ _)
        (sortedAngleAt_nonneg _ _) (sortedAngleAt_lt_pi _ _)
        htie_at_idx htie)
        (fun h => hne_idx (sortedAngleAt_strictMono points |>.injective h))
    rw [hidx_eq_j] at hangle_eq
    intro heq; linarith [interEventAngle_lt_sortedAngle hne j, hθ.2,
      show (direction (L.point a) (L.point b)).angle = sortedAngleAt points j from hangle_eq]

/-! ### Injectivity at inter-event angles -/



/-! ### ConcreteGAS assembly -/

 theorem inj_at_interEventAngle {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin ((directionsDeterminedBy points).card + 1)) :
    Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel (interEventAngle points hne j)
        ((sweepLabeling hcard hne).point a)) := by
  set L := sweepLabeling hcard hne
  rcases eq_or_ne j.val 0 with hj0 | hj0
  · have : j = ⟨0, Nat.succ_pos _⟩ := Fin.ext hj0
    rw [this, interEventAngle_zero]; exact sweepLabeling_inj hcard hne
  · rcases eq_or_ne j.val (directionsDeterminedBy points).card with hjr | hjr
    · have : j = ⟨(directionsDeterminedBy points).card, Nat.lt_succ_self _⟩ := Fin.ext hjr
      rw [this, interEventAngle_last]
      intro a b hab
      have hinj₀ := sweepLabeling_inj hcard hne
      by_contra hneq
      have h₀ : orientedLevel (sweepStartAngle points hne) (L.point a) =
          orientedLevel (sweepStartAngle points hne) (L.point b) := by
        have := orientedLevel_add_pi (sweepStartAngle points hne) (L.point a)
        have := orientedLevel_add_pi (sweepStartAngle points hne) (L.point b)
        linarith
      exact hneq (hinj₀ h₀)
    · have hj_lt : j.val < (directionsDeterminedBy points).card := by
        have := j.isLt; omega
      have hj0' : 0 < j.val := Nat.pos_of_ne_zero hj0
      have hge : 0 ≤ interEventAngle points hne j := by
        have hpred : j.val - 1 < (directionsDeterminedBy points).card := by
          have := j.isLt; omega
        have hprev := sortedAngle_lt_interEventAngle_succ hne ⟨j.val - 1, hpred⟩
        have hval_eq : (⟨(⟨j.val - 1, hpred⟩ : Fin _).val + 1,
            lt_of_eq_of_lt (Nat.succ_pred_eq_of_pos hj0') (j.isLt)⟩ : Fin _) = j :=
          Fin.ext (Nat.succ_pred_eq_of_pos hj0')
        rw [hval_eq] at hprev
        linarith [sortedAngleAt_nonneg points ⟨j.val - 1, hpred⟩]
      have hlt : interEventAngle points hne j < Real.pi := by
        linarith [interEventAngle_lt_sortedAngle hne ⟨j.val, hj_lt⟩,
                  sortedAngleAt_lt_pi points ⟨j.val, hj_lt⟩]
      exact orientedLevel_injective_at_non_direction_angle L hge hlt (by
        intro d hd habs
        rcases direction_angle_eq_sortedAngleAt d hd with ⟨idx, hangle_eq⟩
        rw [hangle_eq] at habs
        have hpred' : j.val - 1 < (directionsDeterminedBy points).card := by
          have := j.isLt; omega
        have h1 := interEventAngle_lt_sortedAngle hne ⟨j.val, hj_lt⟩
        have h2 := sortedAngle_lt_interEventAngle_succ hne ⟨j.val - 1, hpred'⟩
        have hconv' : (⟨(⟨j.val - 1, hpred'⟩ : Fin _).val + 1,
            lt_of_eq_of_lt (Nat.succ_pred_eq_of_pos hj0') (Nat.lt_succ_of_lt hj_lt)⟩ :
            Fin _) = j := Fin.ext (Nat.succ_pred_eq_of_pos hj0')
        rw [hconv'] at h2
        rcases lt_trichotomy idx.val j.val with h | h | h
        · linarith [(sortedAngleAt_strictMono points).monotone
              (show idx ≤ ⟨j.val - 1, hpred'⟩ from
                Fin.le_def.mpr (Nat.le_sub_one_of_lt h))]
        · have : idx = ⟨j.val, hj_lt⟩ := Fin.ext h
          linarith [show sortedAngleAt points idx = sortedAngleAt points ⟨j.val, hj_lt⟩ from
            congr_arg _ this]
        · linarith [(sortedAngleAt_strictMono points)
            (show (⟨j.val, hj_lt⟩ : Fin _) < idx from Fin.lt_def.mpr h)])

/-! ### Monotonicity and nontrivial blocks at events -/

 theorem mono_at_event {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin (directionsDeterminedBy points).card) :
    Monotone (fun i => orientedLevel (sortedAngleAt points j)
      ((sweepLabeling hcard hne).point
        (sweepSort (sweepLabeling hcard hne)
          (interEventAngle points hne ⟨j.val, by omega⟩) i))) := by
  apply sweepSort_event_level_monotone
  · exact inj_at_interEventAngle hcard hne ⟨j.val, by omega⟩
  · exact le_of_lt (interEventAngle_lt_sortedAngle hne j)
  · intro a b hab θ hθ
    have hθ_range : θ ∈ Set.Ioo (interEventAngle points hne ⟨j.val, by omega⟩)
        (sortedAngleAt points j) := hθ
    exact only_event_between_interEventAngles (sweepLabeling hcard hne) hne j a b
      (fun h => hab ((sweepLabeling hcard hne).point_injective h))
      ⟨le_of_lt hθ_range.1, le_of_lt (lt_trans hθ_range.2
        (sortedAngle_lt_interEventAngle_succ hne j))⟩
      (ne_of_lt hθ_range.2)

 theorem nontrivial_blocks_at_event {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin (directionsDeterminedBy points).card) :
    (nontrivialLevelValues (fun i => orientedLevel (sortedAngleAt points j)
      ((sweepLabeling hcard hne).point
        (sweepSort (sweepLabeling hcard hne)
          (interEventAngle points hne ⟨j.val, by omega⟩) i)))).Nonempty := by
  set L := sweepLabeling hcard hne
  set g : Fin (2 * k) → ℝ := fun i => orientedLevel (sortedAngleAt points j)
    (L.point (sweepSort L (interEventAngle points hne ⟨j.val, by omega⟩) i))
  set σ := sweepSort L (interEventAngle points hne ⟨j.val, by omega⟩)
  rcases Finset.mem_image.mp (sortedAngleAt_mem points j) with ⟨d, hd, hangle⟩
  rcases (mem_directionsDeterminedBy_iff_exists_equal_level).mp hd with
    ⟨p, hp, q, hq, hpq_ne, hlevel⟩
  rcases L.point_surjective_on p hp with ⟨a, ha⟩
  rcases L.point_surjective_on q hq with ⟨b, hb⟩
  have hab : a ≠ b := fun h => hpq_ne (by rw [← ha, ← hb, h])
  have hdir_eq : direction p q = d := direction_eq_of_directionLevel_eq hpq_ne hlevel
  have htie_pq := orientedLevel_eq_at_direction_angle hpq_ne
  rw [hdir_eq, hangle] at htie_pq
  have htie : g (σ.symm a) = g (σ.symm b) := by
    show orientedLevel _ (L.point (σ (σ.symm a))) =
      orientedLevel _ (L.point (σ (σ.symm b)))
    simp only [Equiv.apply_symm_apply, ha, hb]; exact htie_pq
  have hii' : σ.symm a ≠ σ.symm b := fun h => hab (σ.symm.injective h)
  rcases lt_or_gt_of_ne hii' with h | h
  · have hhi_ge : σ.symm b ≤ levelBlockHi g (σ.symm a) :=
      le_levelBlockHi_of_monotone_eq' (mono_at_event hcard hne j) htie.symm
    have hlt : (levelBlockLo g (σ.symm a)).val < (levelBlockHi g (σ.symm a)).val :=
      lt_of_le_of_lt (Fin.le_def.mp (levelBlockLo_le (f := g))) (lt_of_lt_of_le h (Fin.le_def.mp hhi_ge))
    exact ⟨g (σ.symm a), mem_nontrivialLevelValues_of_nontrivial_block hlt⟩
  · have hhi_ge : σ.symm a ≤ levelBlockHi g (σ.symm b) :=
      le_levelBlockHi_of_monotone_eq' (mono_at_event hcard hne j) htie
    have hlt : (levelBlockLo g (σ.symm b)).val < (levelBlockHi g (σ.symm b)).val :=
      lt_of_le_of_lt (Fin.le_def.mp (levelBlockLo_le (f := g))) (lt_of_lt_of_le h (Fin.le_def.mp hhi_ge))
    exact ⟨g (σ.symm b), mem_nontrivialLevelValues_of_nontrivial_block hlt⟩

/-! ### ConcreteGAS assembly -/

noncomputable def sweepConcreteGAS {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points) :
    ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy points).card := by
  set L := sweepLabeling hcard hne
  set A := sweepGAS hcard hne hncoll
  let step : ∀ j : Fin (directionsDeterminedBy points).card,
      ReversalStep k (A.π (stepFrom j)) (A.π (stepTo j)) :=
    fun j => sweepReversalStep L
      (sweepLabeling_inj hcard hne)
      (inj_at_interEventAngle hcard hne ⟨j.val, by omega⟩)
      (inj_at_interEventAngle hcard hne ⟨j.val + 1, by omega⟩)
      (sweepLabeling_id hcard hne)
      (interEventAngle_lt_sortedAngle hne j)
      (sortedAngle_lt_interEventAngle_succ hne j)
      (interEventAngle_span hne hr j)
      (fun a b hab θ hθ hθ_ne =>
        only_event_between_interEventAngles L hne j a b hab hθ hθ_ne)
      (fun a b hab htie θ hθ =>
        no_tie_from_start_to_interEvent L hne j a b hab htie hθ)
      (sweepStartAngle_le_interEventAngle hne (stepFrom j))
      (mono_at_event hcard hne j)
      (nontrivial_blocks_at_event hcard hne j)
  let hrev : ∀ j, (step j).move.ReversesBlocks :=
    fun j => @levelBlockMoveOfMonotone_reversesBlocks _ _ (mono_at_event hcard hne j)
      (nontrivial_blocks_at_event hcard hne j)
  exact {
    toCountedGeneralizedAllowableSequence :=
      CountedGeneralizedAllowableSequence.ofReversesBlocks A step hrev
    reversesBlocks := hrev
  }



/-! ### Step directions -/

noncomputable def sweepStepDir (points : Finset Point2)
    (j : Fin (directionsDeterminedBy points).card) : Direction :=
  (Finset.mem_image.mp (sortedAngleAt_mem points j)).choose



theorem sweepStepDir_angle (points : Finset Point2)
    (j : Fin (directionsDeterminedBy points).card) :
    (sweepStepDir points j).angle = sortedAngleAt points j :=
  (Finset.mem_image.mp (sortedAngleAt_mem points j)).choose_spec.2

theorem sweepStepDir_injective (points : Finset Point2) :
    Function.Injective (sweepStepDir points) := by
  intro i j hij
  have hi := sweepStepDir_angle points i
  have hj := sweepStepDir_angle points j
  have hangle_eq : sortedAngleAt points i = sortedAngleAt points j := by
    rw [← hi, ← hj, hij]
  exact (sortedAngleAt_strictMono points).injective hangle_eq

/-! ### BlocksHaveCommonLevel -/

theorem directionLevel_eq_of_orientedLevel_eq_at_direction_angle
    {d : Direction} {p q : Point2}
    (h : orientedLevel d.angle p = orientedLevel d.angle q) :
    directionLevel d p = directionLevel d q := by
  cases d with
  | vertical =>
    simp [orientedLevel, Direction.angle, Real.sin_pi_div_two, Real.cos_pi_div_two] at h
    simp [directionLevel]; linarith
  | finite m =>
    have hcos_ne : Real.cos (Direction.finite m).angle ≠ 0 := by
      simp only [Direction.angle]
      split_ifs with h
      · exact ne_of_gt (Real.cos_arctan_pos m)
      · rw [Real.cos_add, Real.cos_pi, Real.sin_pi]
        simp; exact ne_of_lt (Real.cos_arctan_pos m) |>.symm
    have htan_eq : Direction.finite (Real.tan (Direction.finite m).angle) =
        Direction.finite m := by
      congr 1; simp only [Direction.angle]
      split_ifs with h
      · exact Real.tan_arctan m
      · rw [Real.tan_add_pi]; exact Real.tan_arctan m
    rw [orientedLevel_eq_cos_mul_directionLevel hcos_ne,
        orientedLevel_eq_cos_mul_directionLevel hcos_ne] at h
    rw [← htan_eq]
    exact mul_left_cancel₀ hcos_ne h

theorem sweepConcreteGAS_blocksHaveCommonLevel {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points) :
    (sweepConcreteGAS hcard hne hr hncoll).BlocksHaveCommonLevel
      (sweepLabeling hcard hne) (sweepStepDir points) := by
  set L := sweepLabeling hcard hne
  set CGAS := sweepConcreteGAS hcard hne hr hncoll
  intro j b
  set σ := CGAS.seq.π (stepFrom j)
  set g : Fin (2 * k) → ℝ := fun i => orientedLevel (sortedAngleAt points j) (L.point (σ i))
  set blk := (CGAS.step j).toReversalStep.move.block b
  have hg_mono := mono_at_event hcard hne j
  refine ⟨directionLevel (sweepStepDir points j) (L.point (σ
      ⟨blk.lo, lt_of_le_of_lt blk.lo_le_hi blk.hi_lt⟩)), ?_⟩
  intro p hp
  have hg_eq : g p = g ⟨blk.lo, lt_of_le_of_lt blk.lo_le_hi blk.hi_lt⟩ :=
    @same_g_value_of_same_block _ _ hg_mono (nontrivial_blocks_at_event hcard hne j)
      b p ⟨blk.lo, lt_of_le_of_lt blk.lo_le_hi blk.hi_lt⟩ hp
      ⟨le_refl _, blk.lo_le_hi⟩
  exact directionLevel_eq_of_orientedLevel_eq_at_direction_angle (by
    show orientedLevel (sweepStepDir points j).angle (L.point (σ p)) =
      orientedLevel (sweepStepDir points j).angle (L.point (σ ⟨blk.lo, _⟩))
    rw [sweepStepDir_angle]; exact hg_eq)

theorem directionsDeterminedBy_nonempty_of_noncollinear {points : Finset Point2}
    (hncoll : NoncollinearSet points) :
    (directionsDeterminedBy points).Nonempty := by
  rcases hncoll with ⟨p, hp, q, hq, _, _, hnon⟩
  exact ⟨direction p q, direction_mem_directionsDeterminedBy hp hq
    (left_ne_right_of_noncollinear hnon)⟩

theorem directionsDeterminedBy_card_ge_two_of_noncollinear {points : Finset Point2}
    (hncoll : NoncollinearSet points) :
    2 ≤ (directionsDeterminedBy points).card := by
  rcases hncoll with ⟨p, hp, q, hq, r, hr, hnon⟩
  have hpq := left_ne_right_of_noncollinear hnon
  have hpr := left_ne_third_of_noncollinear hnon
  have hdir_ne := directions_from_noncollinear_triple_ne hnon
  have h1 := direction_mem_directionsDeterminedBy hp hq hpq
  have h2 := direction_mem_directionsDeterminedBy hp hr hpr
  exact Finset.one_lt_card.mpr ⟨_, h1, _, h2, hdir_ne⟩

noncomputable def ungarLevelSweepCore {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hncoll : NoncollinearSet points) :
    UngarLevelSweepCore points k where
  labeling := sweepLabeling hcard (directionsDeterminedBy_nonempty_of_noncollinear hncoll)
  sequence := sweepConcreteGAS hcard
    (directionsDeterminedBy_nonempty_of_noncollinear hncoll)
    (directionsDeterminedBy_card_ge_two_of_noncollinear hncoll) hncoll
  stepDir := sweepStepDir points
  blocks_level := sweepConcreteGAS_blocksHaveCommonLevel hcard
    (directionsDeterminedBy_nonempty_of_noncollinear hncoll)
    (directionsDeterminedBy_card_ge_two_of_noncollinear hncoll) hncoll
  stepDir_injective := sweepStepDir_injective points

abbrev EvenSweepCyclicEndGapPremise : Prop :=
  ∀ S : Finset Point2, ∀ k : ℕ, ∀ hk : 0 < k, ∀ hcard : S.card = 2 * k,
    ∀ hncoll : NoncollinearSet S,
      let C := ungarLevelSweepCore (points := S) (k := k) hcard hncoll
      C.sequence.CyclicEndGap
        (C.sequence.toCountedGeneralizedAllowableSequence.crossingMoves_card_pos hk)





/-!
### Certificate assembly status

The rotating-level sweep constructs `ungarLevelSweepCore`; the cyclic end gap is
then supplied by the shifted-sweep witness assembled below:

- `labeling` = `sweepLabeling`
- `sequence` = `sweepConcreteGAS`
- `stepDir` = `sweepStepDir`
- `blocks_level` = `sweepConcreteGAS_blocksHaveCommonLevel`
- `stepDir_injective` = `sweepStepDir_injective`
- `cyclic_end_gap` = `sweepConcreteGAS_cyclicEndGap_of_noFull`

The theorem `evenSweepCyclicEndGapPremise` discharges the last sweep premise,
and `chapter11` is now the unconditional projective-direction lower bound.
-/

/-! ### Parameterized sweep for CyclicEndGap -/

noncomputable def sweepLabelingAt {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k) (θ₀ : ℝ) : PointLabeling points k :=
  (PointLabeling.ofCard hcard).reindex (sweepSort (PointLabeling.ofCard hcard) θ₀)

noncomputable def shiftedSortedAngleAt (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (s : Fin (directionsDeterminedBy points).card)
    (j : Fin (directionsDeterminedBy points).card) : ℝ :=
  let r := (directionsDeterminedBy points).card
  let idx : Fin r := ⟨(s.val + j.val) % r, Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩
  let θ := sortedAngleAt points idx
  if s.val + j.val < r then θ else θ + Real.pi

 noncomputable def shiftedIndexOfSortedIndex {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s : Fin (directionsDeterminedBy points).card)
    (idx : Fin (directionsDeterminedBy points).card) :
    Fin (directionsDeterminedBy points).card :=
  let r := (directionsDeterminedBy points).card
  if h : idx.val < s.val then
    ⟨idx.val + r - s.val, by
      have hr : 0 < r := by simpa [r] using Finset.card_pos.mpr hne
      have hs : s.val < r := by simp [r]
      omega⟩
  else
    ⟨idx.val - s.val, by
      have hr : 0 < r := by simpa [r] using Finset.card_pos.mpr hne
      have hidx : idx.val < r := by simp [r]
      omega⟩

 noncomputable def shiftedEventAngleAtIndex (points : Finset Point2)
    (s : Fin (directionsDeterminedBy points).card)
    (idx : Fin (directionsDeterminedBy points).card) : ℝ :=
  if idx.val < s.val then sortedAngleAt points idx + Real.pi else sortedAngleAt points idx

 theorem shiftedSortedAngleAt_shiftedIndexOfSortedIndex {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s idx : Fin (directionsDeterminedBy points).card) :
    shiftedSortedAngleAt points hne s (shiftedIndexOfSortedIndex hne s idx) =
      shiftedEventAngleAtIndex points s idx := by
  let r := (directionsDeterminedBy points).card
  have hr : 0 < r := by simpa [r] using Finset.card_pos.mpr hne
  by_cases hidxs : idx.val < s.val
  · have hval :
        (shiftedIndexOfSortedIndex hne s idx).val = idx.val + r - s.val := by
        simp [shiftedIndexOfSortedIndex, r, hidxs]
    have hsum : s.val + (shiftedIndexOfSortedIndex hne s idx).val = idx.val + r := by
      rw [hval]
      have hs_le : s.val ≤ idx.val + r := by omega
      omega
    have hwrap : ¬ s.val + (shiftedIndexOfSortedIndex hne s idx).val < r := by
      rw [hsum]
      omega
    have hmod : (s.val + (shiftedIndexOfSortedIndex hne s idx).val) % r = idx.val := by
      rw [hsum, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by simp [r])
    have hfin :
        (⟨(s.val + (shiftedIndexOfSortedIndex hne s idx).val) %
            (directionsDeterminedBy points).card,
          Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩ :
            Fin (directionsDeterminedBy points).card) = idx := by
      apply Fin.ext
      simpa [r] using hmod
    simp [shiftedSortedAngleAt, shiftedEventAngleAtIndex, r, hidxs, hwrap, hfin]
  · have hval :
        (shiftedIndexOfSortedIndex hne s idx).val = idx.val - s.val := by
        simp [shiftedIndexOfSortedIndex, hidxs]
    have hsum : s.val + (shiftedIndexOfSortedIndex hne s idx).val = idx.val := by
      rw [hval]
      omega
    have hwrap : s.val + (shiftedIndexOfSortedIndex hne s idx).val < r := by
      rw [hsum]
      simp [r]
    have hmod : (s.val + (shiftedIndexOfSortedIndex hne s idx).val) % r = idx.val := by
      rw [hsum]
      exact Nat.mod_eq_of_lt (by simp [r])
    have hfin :
        (⟨(s.val + (shiftedIndexOfSortedIndex hne s idx).val) %
            (directionsDeterminedBy points).card,
          Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩ :
            Fin (directionsDeterminedBy points).card) = idx := by
      apply Fin.ext
      simpa [r] using hmod
    simp [shiftedSortedAngleAt, shiftedEventAngleAtIndex, r, hidxs, hwrap, hfin]

noncomputable def interEventAngleAt (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ)
    (s : Fin (directionsDeterminedBy points).card)
    (j : Fin ((directionsDeterminedBy points).card + 1)) : ℝ :=
  if hj0 : j.val = 0 then θ₀
  else if hjr : j.val = (directionsDeterminedBy points).card then θ₀ + Real.pi
  else
    let r := (directionsDeterminedBy points).card
    let j_prev : Fin r := ⟨j.val - 1, by omega⟩
    let j_cur : Fin r := ⟨j.val, by omega⟩
    genericAngleBetween (shiftedSortedAngleAt points hne s j_prev)
      (shiftedSortedAngleAt points hne s j_cur)

theorem interEventAngleAt_zero (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card) :
    interEventAngleAt points hne θ₀ s ⟨0, Nat.succ_pos _⟩ = θ₀ := by
  simp [interEventAngleAt]

theorem interEventAngleAt_last (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card) :
    interEventAngleAt points hne θ₀ s ⟨(directionsDeterminedBy points).card, Nat.lt_succ_self _⟩ = θ₀ + Real.pi := by
  simp only [interEventAngleAt]
  have hne0 : (directionsDeterminedBy points).card ≠ 0 := Finset.card_ne_zero.mpr hne
  simp [hne0]

theorem sweepLabelingAt_id {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (_hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) :
    sweepSort (sweepLabelingAt (points := points) hcard θ₀) θ₀ = Equiv.refl _ :=
  sweepSort_reindex_eq_refl _ _



theorem sweepLabelingAt_inj_mod_pi {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (θ₀ : ℝ)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi)
    (hne_angle : ∀ d ∈ directionsDeterminedBy points, θ₀ ≠ d.angle) :
    Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel θ₀ ((sweepLabelingAt (points := points) hcard θ₀).point a)) :=
  orientedLevel_injective_of_all_angles_mod_pi _ hlow hhigh hne_angle



noncomputable def sweepGAS_at_mod_pi {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ)
    (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi)
    (hne_angle : ∀ d ∈ directionsDeterminedBy points, θ₀ ≠ d.angle)
    (_hncoll : NoncollinearSet points) :
    GeneralizedAllowableSequence k (directionsDeterminedBy points).card :=
  GeneralizedAllowableSequence.ofSweepAngles
    (sweepLabelingAt hcard θ₀)
    (interEventAngleAt points hne θ₀ s)
    (by rw [interEventAngleAt_zero]; exact sweepLabelingAt_id hcard hne θ₀)
    (by rw [interEventAngleAt_last, interEventAngleAt_zero])
    (by rw [interEventAngleAt_zero]
        exact sweepLabelingAt_inj_mod_pi hcard θ₀ hlow hhigh hne_angle)




theorem shiftedSortedAngleAt_lt_succ {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s : Fin (directionsDeterminedBy points).card)
    (j : Fin (directionsDeterminedBy points).card)
    (hj : j.val + 1 < (directionsDeterminedBy points).card) :
    shiftedSortedAngleAt points hne s j <
      shiftedSortedAngleAt points hne s ⟨j.val + 1, by omega⟩ := by
  let r : ℕ := (directionsDeterminedBy points).card
  have hr0 : 0 < r := by
    simpa [r] using Finset.card_pos.mpr hne
  by_cases h0 : s.val + j.val < r
  · by_cases h1 : s.val + (j.val + 1) < r
    · have hmod0 : (s.val + j.val) % r = s.val + j.val := Nat.mod_eq_of_lt h0
      have hmod1 : (s.val + (j.val + 1)) % r = s.val + (j.val + 1) :=
        Nat.mod_eq_of_lt h1
      have hlt_nat : s.val + j.val < s.val + (j.val + 1) := by
        simp
      have hlt : sortedAngleAt points ⟨s.val + j.val, by omega⟩ <
          sortedAngleAt points ⟨s.val + (j.val + 1), by omega⟩ :=
        sortedAngleAt_strictMono points (Fin.lt_def.mpr hlt_nat)
      simpa [shiftedSortedAngleAt, r, h0, h1, hmod0, hmod1]
        using hlt
    · have hsum : s.val + (j.val + 1) = r := by omega
      have hmod0 : (s.val + j.val) % r = s.val + j.val := Nat.mod_eq_of_lt h0
      have hmod1 : (s.val + (j.val + 1)) % r = 0 := by simp [hsum]
      have hlt : sortedAngleAt points ⟨s.val + j.val, by omega⟩ < Real.pi :=
        sortedAngleAt_lt_pi points ⟨s.val + j.val, by omega⟩
      have hnonneg : 0 ≤ sortedAngleAt points (⟨0, Nat.zero_lt_of_lt hr0⟩) :=
        sortedAngleAt_nonneg points (⟨0, Nat.zero_lt_of_lt hr0⟩)
      have hlt' :
          sortedAngleAt points ⟨s.val + j.val, by omega⟩ <
            sortedAngleAt points (⟨0, Nat.zero_lt_of_lt hr0⟩) + Real.pi :=
        by linarith
      simpa [shiftedSortedAngleAt, r, h0, hsum, hmod0, hmod1]
        using hlt'
  · have h1 : ¬ s.val + (j.val + 1) < r := by omega
    have hmod0 : (s.val + j.val) % r = s.val + j.val - r := by
      have hle0 : r ≤ s.val + j.val := Nat.le_of_not_lt h0
      have hlt0 : s.val + j.val - r < r := by omega
      rw [Nat.mod_eq_sub_mod hle0, Nat.mod_eq_of_lt hlt0]
    have hmod1 : (s.val + (j.val + 1)) % r = s.val + (j.val + 1) - r := by
      have hle1 : r ≤ s.val + (j.val + 1) := by omega
      have hlt1 : s.val + (j.val + 1) - r < r := by omega
      rw [Nat.mod_eq_sub_mod hle1, Nat.mod_eq_of_lt hlt1]
    have hlt_nat : s.val + j.val - r < s.val + (j.val + 1) - r := by omega
    have hlt : sortedAngleAt points ⟨s.val + j.val - r, by omega⟩ <
        sortedAngleAt points ⟨s.val + (j.val + 1) - r, by omega⟩ :=
      sortedAngleAt_strictMono points (Fin.lt_def.mpr hlt_nat)
    have hlt' : sortedAngleAt points ⟨s.val + j.val - r, by omega⟩ + Real.pi <
        sortedAngleAt points ⟨s.val + (j.val + 1) - r, by omega⟩ + Real.pi :=
      by linarith [hlt]
    simpa [shiftedSortedAngleAt, r, h0, h1, hmod0, hmod1] using hlt'

 theorem shiftedSortedAngleAt_strictMono {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s : Fin (directionsDeterminedBy points).card) :
    StrictMono (fun i : Fin (directionsDeterminedBy points).card =>
      shiftedSortedAngleAt points hne s i) := by
  let r : ℕ := (directionsDeterminedBy points).card
  have hr : 0 < r := by simpa [r] using Finset.card_pos.mpr hne
  have hsub : (r - 1 + 1) = r := Nat.sub_add_cancel (Nat.succ_le_of_lt hr)
  let down : Fin (r - 1 + 1) → Fin (directionsDeterminedBy points).card :=
    fun i => ⟨i.1, by simpa [r, hsub] using i.isLt⟩
  let up : Fin (directionsDeterminedBy points).card → Fin (r - 1 + 1) :=
    fun i => ⟨i.1, by simp [r, hsub]⟩
  have hmono' : StrictMono (fun i : Fin (r - 1 + 1) =>
      shiftedSortedAngleAt points hne s (down i)) := by
    refine (Fin.strictMono_iff_lt_succ).2 ?_
    intro i
    have hj_lt : i.val < (directionsDeterminedBy points).card := by
      omega
    have hsucc_lt : i.val + 1 < (directionsDeterminedBy points).card := by
      omega
    have hlt := shiftedSortedAngleAt_lt_succ (points := points) hne s
      (j := ⟨i.val, hj_lt⟩) hsucc_lt
    simpa [down] using hlt
  intro i j hij
  have hlt : up i < up j := by
    exact Fin.lt_def.2 (by simpa [up] using Fin.lt_def.1 hij)
  have htmp : shiftedSortedAngleAt points hne s (down (up i)) <
      shiftedSortedAngleAt points hne s (down (up j)) :=
    hmono' hlt
  simpa [up, down] using htmp



 theorem shiftedSortedAngleAt_gt_start_mod_pi {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi) :
    ∀ t : Fin (directionsDeterminedBy points).card,
      θ₀ < shiftedSortedAngleAt points hne s t := by
  intro t
  let r : ℕ := (directionsDeterminedBy points).card
  have hr : 0 < r := by simpa [r] using Finset.card_pos.mpr hne
  set idx : Fin r := ⟨(s.val + t.val) % r, Nat.mod_lt _ hr⟩
  by_cases hwrap : s.val + t.val < r
  · have hmod : (s.val + t.val) % r = s.val + t.val := Nat.mod_eq_of_lt hwrap
    have hidx_ge : s.val ≤ idx.val := by
      dsimp [idx]
      rw [hmod]
      omega
    have hlt := hafter idx (by simpa [r] using hidx_ge)
    simpa [shiftedSortedAngleAt, r, idx, hwrap] using hlt
  · have hge : r ≤ s.val + t.val := Nat.le_of_not_lt hwrap
    have hmod : (s.val + t.val) % r = s.val + t.val - r := by
      rw [Nat.mod_eq_sub_mod hge]
      exact Nat.mod_eq_of_lt (by omega)
    rcases Finset.mem_image.mp (sortedAngleAt_mem points idx) with ⟨d, hd, hangle⟩
    have hlt : θ₀ < sortedAngleAt points idx + Real.pi := by
      simpa [r, idx, hangle] using hhigh d hd
    simpa [shiftedSortedAngleAt, r, idx, hwrap, hmod] using hlt

 theorem shiftedSortedAngleAt_lt_start_add_pi_mod_pi {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀) :
    ∀ t : Fin (directionsDeterminedBy points).card,
      shiftedSortedAngleAt points hne s t < θ₀ + Real.pi := by
  intro t
  let r : ℕ := (directionsDeterminedBy points).card
  have hr : 0 < r := by simpa [r] using Finset.card_pos.mpr hne
  set idx : Fin r := ⟨(s.val + t.val) % r, Nat.mod_lt _ hr⟩
  by_cases hwrap : s.val + t.val < r
  · rcases Finset.mem_image.mp (sortedAngleAt_mem points idx) with ⟨d, hd, hangle⟩
    have hlow' : sortedAngleAt points idx - Real.pi < θ₀ := by
      simpa [r, idx, hangle] using hlow d hd
    have hlt : sortedAngleAt points idx < θ₀ + Real.pi := by linarith
    simpa [shiftedSortedAngleAt, r, idx, hwrap] using hlt
  · have hge : r ≤ s.val + t.val := Nat.le_of_not_lt hwrap
    have hmod : (s.val + t.val) % r = s.val + t.val - r := by
      rw [Nat.mod_eq_sub_mod hge]
      exact Nat.mod_eq_of_lt (by omega)
    have hidx_lt : idx.val < s.val := by
      dsimp [idx]
      rw [hmod]
      omega
    have hbefore' : sortedAngleAt points idx < θ₀ :=
      hbefore idx (by simpa [r] using hidx_lt)
    have hlt : sortedAngleAt points idx + Real.pi < θ₀ + Real.pi := by linarith
    simpa [shiftedSortedAngleAt, r, idx, hwrap, hmod] using hlt






theorem interEventAngleAt_lt_shiftedSortedAngle_mod_pi
    (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi) :
    ∀ j : Fin (directionsDeterminedBy points).card,
    interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩ <
      shiftedSortedAngleAt points hne s j := by
  intro j
  have hcard : 0 < (directionsDeterminedBy points).card := Finset.card_pos.mpr hne
  by_cases hj0 : j.val = 0
  · have hlow_start : θ₀ < shiftedSortedAngleAt points hne s ⟨0, hcard⟩ :=
      shiftedSortedAngleAt_gt_start_mod_pi (points := points) hne θ₀ s hafter hhigh
        ⟨0, hcard⟩
    have hj0' : (⟨j.val, by omega⟩ : Fin ((directionsDeterminedBy points).card + 1)) =
        ⟨0, Nat.succ_pos _⟩ := Fin.ext hj0
    have hjs : (j : Fin (directionsDeterminedBy points).card) = ⟨0, hcard⟩ := Fin.ext hj0
    simpa [interEventAngleAt_zero, hj0', hjs] using hlow_start
  · have hnotlast : j.val ≠ (directionsDeterminedBy points).card := by omega
    have hpred_lt : (j.val - 1) + 1 < (directionsDeterminedBy points).card := by
      simp [Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)]
    have hlt0 : shiftedSortedAngleAt points hne s ⟨j.val - 1, by omega⟩ <
        shiftedSortedAngleAt points hne s ⟨(j.val - 1) + 1, by omega⟩ :=
      shiftedSortedAngleAt_lt_succ (points := points) hne s ⟨j.val - 1, by omega⟩ hpred_lt
    have hlt : shiftedSortedAngleAt points hne s ⟨j.val - 1, by omega⟩ <
        shiftedSortedAngleAt points hne s j := by
      have hidx :
          (⟨(j.val - 1) + 1, by omega⟩ : Fin (directionsDeterminedBy points).card) = j :=
        by
          apply Fin.ext
          exact Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0)
      simpa [hidx] using hlt0
    have hrepr : interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩ =
        genericAngleBetween (shiftedSortedAngleAt points hne s ⟨j.val - 1, by omega⟩)
          (shiftedSortedAngleAt points hne s j) := by
      simp [interEventAngleAt, hnotlast, hj0]
    rw [hrepr]
    exact genericAngleBetween_lt' hlt

theorem shiftedSortedAngleAt_lt_interEventAngleAt_succ_mod_pi
    (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀) :
    ∀ j : Fin (directionsDeterminedBy points).card,
    shiftedSortedAngleAt points hne s j <
      interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩ := by
  intro j
  by_cases hjr : j.val + 1 = (directionsDeterminedBy points).card
  · have hle : shiftedSortedAngleAt points hne s j < θ₀ + Real.pi :=
      shiftedSortedAngleAt_lt_start_add_pi_mod_pi (points := points)
        hne θ₀ s hlow hbefore j
    have hlast : interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩ = θ₀ + Real.pi := by
      have hjlast : (⟨j.val + 1, by omega⟩ : Fin ((directionsDeterminedBy points).card + 1)) =
        ⟨(directionsDeterminedBy points).card, Nat.lt_succ_self _⟩ := Fin.ext hjr
      rw [hjlast]
      exact interEventAngleAt_last (points := points) hne θ₀ s
    linarith [hle, hlast]
  · have hne2 : ¬ (j.val + 1 = 0) := by omega
    have hlt : shiftedSortedAngleAt points hne s j <
        shiftedSortedAngleAt points hne s ⟨j.val + 1, by omega⟩ :=
      shiftedSortedAngleAt_lt_succ (points := points) hne s j (by omega)
    simpa [interEventAngleAt, hne2, hjr] using (genericAngleBetween_lt hlt)





theorem interEventAngleAt_le_start_add_pi_mod_pi
    (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi) :
    ∀ j : Fin ((directionsDeterminedBy points).card + 1),
    interEventAngleAt points hne θ₀ s j ≤ θ₀ + Real.pi := by
  intro j
  by_cases hjr : j.val = (directionsDeterminedBy points).card
  · have hj0 : j.val ≠ 0 := by
      have hr : 0 < (directionsDeterminedBy points).card := Finset.card_pos.mpr hne
      omega
    have hlast : interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩ = θ₀ + Real.pi := by
      have hj1 : (⟨j.val, by omega⟩ : Fin ((directionsDeterminedBy points).card + 1)) =
        ⟨(directionsDeterminedBy points).card, Nat.lt_succ_self _⟩ := Fin.ext hjr
      rw [hj1]
      simpa [interEventAngleAt, hj0] using (interEventAngleAt_last (points := points) hne θ₀ s)
    exact hlast.le
  · have hj_lt : j.val < (directionsDeterminedBy points).card := by omega
    have hlt :
      interEventAngleAt points hne θ₀ s j < shiftedSortedAngleAt points hne s ⟨j.val, hj_lt⟩ :=
      interEventAngleAt_lt_shiftedSortedAngle_mod_pi (points := points)
        hne θ₀ s hafter hhigh ⟨j.val, hj_lt⟩
    have hbound :
        shiftedSortedAngleAt points hne s ⟨j.val, hj_lt⟩ < θ₀ + Real.pi :=
      shiftedSortedAngleAt_lt_start_add_pi_mod_pi (points := points)
        hne θ₀ s hlow hbefore ⟨j.val, hj_lt⟩
    exact le_of_lt (lt_trans hlt hbound)

theorem startAngle_le_interEventAngleAt_mod_pi
    (points : Finset Point2)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi) :
    ∀ j : Fin ((directionsDeterminedBy points).card + 1),
    θ₀ ≤ interEventAngleAt points hne θ₀ s j := by
  intro j
  by_cases hj0 : j.val = 0
  · have hj0' : j = ⟨0, Nat.succ_pos _⟩ := Fin.ext hj0
    rw [hj0', interEventAngleAt_zero]
  · by_cases hjr : j.val = (directionsDeterminedBy points).card
    · have hj0' : j.val ≠ 0 := by
        have hr : 0 < (directionsDeterminedBy points).card := Finset.card_pos.mpr hne
        omega
      have hlast : interEventAngleAt points hne θ₀ s j = θ₀ + Real.pi := by
        have hjr' : (j : Fin ((directionsDeterminedBy points).card + 1)) =
            ⟨(directionsDeterminedBy points).card, Nat.lt_succ_self _⟩ := Fin.ext hjr
        rw [hjr']
        simpa [interEventAngleAt, hj0'] using (interEventAngleAt_last (points := points) hne θ₀ s)
      rw [hlast]
      linarith [Real.pi_pos]
    · let jp : Fin (directionsDeterminedBy points).card := ⟨j.val - 1, by omega⟩
      have hprev :
          shiftedSortedAngleAt points hne s jp <
            interEventAngleAt points hne θ₀ s ⟨jp.val + 1, by omega⟩ :=
        shiftedSortedAngleAt_lt_interEventAngleAt_succ_mod_pi points hne θ₀ s hlow hbefore jp
      have hprev' :
          shiftedSortedAngleAt points hne s ⟨j.val - 1, by omega⟩ <
            interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩ := by
        have hj_prev : (⟨jp.val + 1, by omega⟩ : Fin ((directionsDeterminedBy points).card + 1)) =
            ⟨j.val, by omega⟩ := by
          apply Fin.ext
          simpa [jp] using (Nat.sub_add_cancel (Nat.pos_of_ne_zero hj0))
        simpa [jp, hj_prev] using hprev
      have hstart : θ₀ < shiftedSortedAngleAt points hne s ⟨j.val - 1, by omega⟩ :=
        shiftedSortedAngleAt_gt_start_mod_pi (points := points) hne θ₀ s hafter hhigh
          ⟨j.val - 1, by omega⟩
      exact le_of_lt (lt_trans hstart hprev')

 theorem interEventAngleAt_no_other_shiftedEventAngle {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (j : Fin (directionsDeterminedBy points).card)
    (idx : Fin (directionsDeterminedBy points).card)
    (h_in : shiftedEventAngleAtIndex points s idx ∈ Set.Icc
        (interEventAngleAt points hne θ₀ s ⟨j.val, by have := j.isLt; omega⟩)
        (interEventAngleAt points hne θ₀ s ⟨j.val + 1, by have := j.isLt; omega⟩))
    (h_ne : shiftedEventAngleAtIndex points s idx ≠ shiftedSortedAngleAt points hne s j) :
    False := by
  let r : ℕ := (directionsDeterminedBy points).card
  have hr : 0 < r := by simpa [r] using Finset.card_pos.mpr hne
  let j0 : Fin (r + 1) := ⟨j.val, by simp [r]⟩
  let j1 : Fin (r + 1) := ⟨j.val + 1, by omega⟩
  let it : Fin (directionsDeterminedBy points).card :=
    shiftedIndexOfSortedIndex hne s idx
  have hshift_it :
      shiftedSortedAngleAt points hne s it = shiftedEventAngleAtIndex points s idx := by
    simpa [it] using shiftedSortedAngleAt_shiftedIndexOfSortedIndex hne s idx
  have h_lower : interEventAngleAt points hne θ₀ s j0 ≤
      shiftedSortedAngleAt points hne s it := by
    simpa [j0, hshift_it] using h_in.1
  have h_upper : shiftedSortedAngleAt points hne s it ≤
      interEventAngleAt points hne θ₀ s j1 := by
    simpa [j1, hshift_it] using h_in.2
  have hshift_ne : shiftedSortedAngleAt points hne s it ≠
      shiftedSortedAngleAt points hne s j := by
    intro h
    exact h_ne (by simpa [hshift_it] using h)
  have hstrict := shiftedSortedAngleAt_strictMono (points := points) hne s
  rcases lt_trichotomy it j with hlt | hEq | hgt
  · have hj0 : j.val ≠ 0 := by omega
    let jprev : Fin r := ⟨j.val - 1, by omega⟩
    have htpred : it ≤ jprev := by
      exact Fin.le_def.2 (by simpa [jprev] using Nat.le_sub_one_of_lt (Fin.lt_def.mp hlt))
    have hpred_le : shiftedSortedAngleAt points hne s it ≤
        shiftedSortedAngleAt points hne s jprev :=
      hstrict.monotone htpred
    have hpred_lt : shiftedSortedAngleAt points hne s jprev <
        shiftedSortedAngleAt points hne s j := by
      have hlt' : jprev < j := by
        exact Fin.lt_def.2 (by
          simpa [jprev] using Nat.sub_one_lt (Nat.ne_of_gt (Nat.pos_of_ne_zero hj0)))
      exact hstrict hlt'
    have hrepr : interEventAngleAt points hne θ₀ s j0 =
        genericAngleBetween (shiftedSortedAngleAt points hne s jprev)
          (shiftedSortedAngleAt points hne s j) := by
      have hj0' : (j0 : Fin (r + 1)).val ≠ 0 := by
        simpa [j0] using hj0
      have h_last : j.val ≠ r := by omega
      by_cases h : j.val = (directionsDeterminedBy points).card
      · exact (h_last (by simpa [r] using h)).elim
      · simp [interEventAngleAt, j0, hj0', h, jprev]
    have h_lt_start : shiftedSortedAngleAt points hne s jprev <
        interEventAngleAt points hne θ₀ s j0 := by
      simpa [hrepr] using (genericAngleBetween_lt hpred_lt)
    have hθ : shiftedSortedAngleAt points hne s it <
        interEventAngleAt points hne θ₀ s j0 := by
      exact lt_of_le_of_lt hpred_le h_lt_start
    exact (not_lt_of_ge h_lower) hθ
  · have hshift_eq : shiftedSortedAngleAt points hne s it =
        shiftedSortedAngleAt points hne s j := by
      simp [hEq]
    exact hshift_ne hshift_eq
  · have hnext : j < it := hgt
    let jnext : Fin r := ⟨j.val + 1, by omega⟩
    have hnext_le : shiftedSortedAngleAt points hne s jnext ≤
        shiftedSortedAngleAt points hne s it := by
      apply hstrict.monotone
      exact Fin.le_def.2 (by
        simpa [jnext] using (Nat.succ_le_of_lt (Fin.lt_def.mp hnext)))
    have hlt' : shiftedSortedAngleAt points hne s j <
        shiftedSortedAngleAt points hne s jnext := by
      have hjlt : j < jnext := by
        exact Fin.lt_def.2 (by simp [jnext])
      exact hstrict hjlt
    have hrepr : interEventAngleAt points hne θ₀ s j1 =
        genericAngleBetween (shiftedSortedAngleAt points hne s j)
          (shiftedSortedAngleAt points hne s jnext) := by
      have hj1_last : j.val + 1 ≠ r := by omega
      have hj1_ne0 : (j1 : Fin (r + 1)).val ≠ 0 := by
        simp [j1]
      by_cases h : j.val + 1 = (directionsDeterminedBy points).card
      · exact (hj1_last (by simpa [r] using h)).elim
      · simp [interEventAngleAt, j1, jnext, h]
    have h_succ_lt : interEventAngleAt points hne θ₀ s j1 <
        shiftedSortedAngleAt points hne s jnext := by
      simpa [hrepr] using (genericAngleBetween_lt' hlt')
    have hθ : interEventAngleAt points hne θ₀ s j1 <
        shiftedSortedAngleAt points hne s it := by
      exact lt_of_lt_of_le h_succ_lt hnext_le
    exact (not_lt_of_ge h_upper) hθ

 theorem shiftedEventAngleAtIndex_tie {points : Finset Point2}
    (s : Fin (directionsDeterminedBy points).card)
    (idx : Fin (directionsDeterminedBy points).card)
    {p q : Point2} (hpq : p ≠ q)
    (hangle : (direction p q).angle = sortedAngleAt points idx) :
    orientedLevel (shiftedEventAngleAtIndex points s idx) p =
      orientedLevel (shiftedEventAngleAtIndex points s idx) q := by
  by_cases hidx : idx.val < s.val
  · have htie := orientedLevel_eq_at_direction_angle hpq
    have htie_neg : -orientedLevel (direction p q).angle p =
        -orientedLevel (direction p q).angle q := by
      exact congrArg Neg.neg htie
    simpa [shiftedEventAngleAtIndex, hidx, ← hangle,
      orientedLevel_add_pi] using htie_neg
  · simpa [shiftedEventAngleAtIndex, hidx, ← hangle]
      using orientedLevel_eq_at_direction_angle hpq

theorem only_event_between_interEventAnglesAt_mod_pi {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi)
    (j : Fin (directionsDeterminedBy points).card)
    (a b : Fin (2 * k)) (hab : L.point a ≠ L.point b)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩)
      (interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩))
    (hθ_ne : θ ≠ shiftedSortedAngleAt points hne s j) :
    orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b) := by
  have hab' : a ≠ b := fun h => hab (congr_arg L.point h)
  have hpq : L.point a ≠ L.point b := fun h => hab' (L.point_injective h)
  have hdir_mem := L.direction_mem hab'
  rcases direction_angle_eq_sortedAngleAt (direction (L.point a) (L.point b)) hdir_mem with
    ⟨idx, hangle_eq⟩
  let δ := shiftedEventAngleAtIndex points s idx
  have hδ_tie : orientedLevel δ (L.point a) = orientedLevel δ (L.point b) := by
    simpa [δ] using shiftedEventAngleAtIndex_tie (points := points) s idx hpq hangle_eq
  have hδ_gt : θ₀ < δ := by
    have hshift := shiftedSortedAngleAt_shiftedIndexOfSortedIndex hne s idx
    have hgt := shiftedSortedAngleAt_gt_start_mod_pi (points := points)
      hne θ₀ s hafter hhigh (shiftedIndexOfSortedIndex hne s idx)
    simpa [δ, hshift] using hgt
  have hδ_lt : δ < θ₀ + Real.pi := by
    have hshift := shiftedSortedAngleAt_shiftedIndexOfSortedIndex hne s idx
    have hlt := shiftedSortedAngleAt_lt_start_add_pi_mod_pi (points := points)
      hne θ₀ s hlow hbefore (shiftedIndexOfSortedIndex hne s idx)
    simpa [δ, hshift] using hlt
  have hθ_ne_delta : θ ≠ δ := by
    intro hθδ
    have hδ_in : δ ∈ Set.Icc
        (interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩)
        (interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩) := by
      simpa [hθδ] using hθ
    by_cases hδ_current : δ = shiftedSortedAngleAt points hne s j
    · exact hθ_ne (hθδ.trans hδ_current)
    · exact interEventAngleAt_no_other_shiftedEventAngle (points := points)
        hne θ₀ s j idx (by simpa [δ] using hδ_in) (by simpa [δ] using hδ_current)
  have hθ_ge_start : θ₀ ≤ θ := by
    have hstart := startAngle_le_interEventAngleAt_mod_pi (points := points)
      hne θ₀ s hlow hbefore hafter hhigh ⟨j.val, by omega⟩
    exact le_trans hstart hθ.1
  have hθ_le_end : θ ≤ θ₀ + Real.pi := by
    have hend := interEventAngleAt_le_start_add_pi_mod_pi (points := points)
      hne θ₀ s hlow hbefore hafter hhigh ⟨j.val + 1, by omega⟩
    exact le_trans hθ.2 hend
  have hθ_lo : δ - Real.pi < θ := by
    linarith [hδ_lt, hθ_ge_start]
  have hθ_hi : θ < δ + Real.pi := by
    linarith [hδ_gt, hθ_le_end]
  exact orientedLevel_ne_of_ne_tie_angle_in_pi_window hpq
    hδ_tie hθ_lo hθ_hi hθ_ne_delta

theorem no_tie_from_start_to_interEventAt_mod_pi {points : Finset Point2} {k : ℕ}
    (L : PointLabeling points k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi)
    (j : Fin (directionsDeterminedBy points).card)
    (a b : Fin (2 * k)) (hab : L.point a ≠ L.point b)
    (htie : orientedLevel (shiftedSortedAngleAt points hne s j) (L.point a) =
      orientedLevel (shiftedSortedAngleAt points hne s j) (L.point b))
    {θ : ℝ} (hθ : θ ∈ Set.Icc θ₀
      (interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩)) :
    orientedLevel θ (L.point a) ≠ orientedLevel θ (L.point b) := by
  have hab' : a ≠ b := fun h => hab (congr_arg L.point h)
  have hpq : L.point a ≠ L.point b := fun h => hab' (L.point_injective h)
  have hdir_mem := L.direction_mem hab'
  rcases direction_angle_eq_sortedAngleAt (direction (L.point a) (L.point b)) hdir_mem with
    ⟨idx, hangle_eq⟩
  let δ := shiftedEventAngleAtIndex points s idx
  have hδ_tie : orientedLevel δ (L.point a) = orientedLevel δ (L.point b) := by
    simpa [δ] using shiftedEventAngleAtIndex_tie (points := points) s idx hpq hangle_eq
  have hδ_gt : θ₀ < δ := by
    have hshift := shiftedSortedAngleAt_shiftedIndexOfSortedIndex hne s idx
    have hgt := shiftedSortedAngleAt_gt_start_mod_pi (points := points)
      hne θ₀ s hafter hhigh (shiftedIndexOfSortedIndex hne s idx)
    simpa [δ, hshift] using hgt
  have hδ_lt : δ < θ₀ + Real.pi := by
    have hshift := shiftedSortedAngleAt_shiftedIndexOfSortedIndex hne s idx
    have hlt := shiftedSortedAngleAt_lt_start_add_pi_mod_pi (points := points)
      hne θ₀ s hlow hbefore (shiftedIndexOfSortedIndex hne s idx)
    simpa [δ, hshift] using hlt
  have hevent_gt : θ₀ < shiftedSortedAngleAt points hne s j :=
    shiftedSortedAngleAt_gt_start_mod_pi (points := points) hne θ₀ s hafter hhigh j
  have hevent_lt : shiftedSortedAngleAt points hne s j < θ₀ + Real.pi :=
    shiftedSortedAngleAt_lt_start_add_pi_mod_pi (points := points) hne θ₀ s hlow hbefore j
  have hδ_eq_event : δ = shiftedSortedAngleAt points hne s j := by
    have hbound : |δ - shiftedSortedAngleAt points hne s j| < Real.pi := by
      rw [abs_lt]
      constructor <;> linarith
    exact orientedLevel_unique_tie_angle_of_abs_sub_lt_pi hpq hbound hδ_tie htie
  have hθ_lt_delta : θ < δ := by
    have hbefore_event :
        interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩ <
          shiftedSortedAngleAt points hne s j :=
      interEventAngleAt_lt_shiftedSortedAngle_mod_pi (points := points)
        hne θ₀ s hafter hhigh j
    linarith [hθ.2, hbefore_event, hδ_eq_event]
  have hθ_ne_delta : θ ≠ δ := ne_of_lt hθ_lt_delta
  have hθ_lo : δ - Real.pi < θ := by
    linarith [hδ_lt, hθ.1]
  have hθ_hi : θ < δ + Real.pi := by
    linarith [hθ_lt_delta, Real.pi_pos]
  exact orientedLevel_ne_of_ne_tie_angle_in_pi_window hpq
    hδ_tie hθ_lo hθ_hi hθ_ne_delta

 theorem inj_at_interEventAngleAt_mod_pi {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi)
    (j : Fin ((directionsDeterminedBy points).card + 1)) :
    Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel (interEventAngleAt points hne θ₀ s j)
        ((sweepLabelingAt (points := points) hcard θ₀).point a)) := by
  set L := sweepLabelingAt (points := points) hcard θ₀
  set θ := interEventAngleAt points hne θ₀ s j with hθ_def
  intro a b hlevel
  by_contra hne_ab
  have ha_ne_b : a ≠ b := fun h => by subst h; exact hne_ab rfl
  have hpq : L.point a ≠ L.point b := fun h => ha_ne_b (L.point_injective h)
  by_cases hj_last : j.val = (directionsDeterminedBy points).card
  · have hj_last' :
        j = ⟨(directionsDeterminedBy points).card, Nat.lt_succ_self _⟩ :=
      Fin.ext hj_last
    have hθ_eq : θ = θ₀ + Real.pi := by
      rw [hθ_def, hj_last']
      exact interEventAngleAt_last (points := points) hne θ₀ s
    have hdir_mem :
        direction (L.point a) (L.point b) ∈ directionsDeterminedBy points :=
      L.direction_mem ha_ne_b
    rcases direction_angle_eq_sortedAngleAt (direction (L.point a) (L.point b)) hdir_mem with
      ⟨idx, hangle_eq⟩
    let δ := shiftedEventAngleAtIndex points s idx
    have hδ_tie : orientedLevel δ (L.point a) = orientedLevel δ (L.point b) := by
      simpa [δ] using shiftedEventAngleAtIndex_tie (points := points) s idx hpq hangle_eq
    have hδ_gt : θ₀ < δ := by
      have hshift := shiftedSortedAngleAt_shiftedIndexOfSortedIndex hne s idx
      have hgt := shiftedSortedAngleAt_gt_start_mod_pi (points := points)
        hne θ₀ s hafter hhigh (shiftedIndexOfSortedIndex hne s idx)
      simpa [δ, hshift] using hgt
    have hδ_lt : δ < θ₀ + Real.pi := by
      have hshift := shiftedSortedAngleAt_shiftedIndexOfSortedIndex hne s idx
      have hlt := shiftedSortedAngleAt_lt_start_add_pi_mod_pi (points := points)
        hne θ₀ s hlow hbefore (shiftedIndexOfSortedIndex hne s idx)
      simpa [δ, hshift] using hlt
    have hθ_ne_delta : θ ≠ δ := by
      intro hθδ
      linarith
    have hθ_lo : δ - Real.pi < θ := by
      linarith
    have hθ_hi : θ < δ + Real.pi := by
      linarith
    exact (orientedLevel_ne_of_ne_tie_angle_in_pi_window hpq
      hδ_tie hθ_lo hθ_hi hθ_ne_delta) hlevel
  · have hj_lt : j.val < (directionsDeterminedBy points).card := by omega
    let jj : Fin (directionsDeterminedBy points).card := ⟨j.val, hj_lt⟩
    have hstep_lt :
        interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩ <
          interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩ :=
      lt_trans
        (interEventAngleAt_lt_shiftedSortedAngle_mod_pi (points := points)
          hne θ₀ s hafter hhigh jj)
        (shiftedSortedAngleAt_lt_interEventAngleAt_succ_mod_pi (points := points)
          hne θ₀ s hlow hbefore jj)
    have hθ_icc : θ ∈ Set.Icc
        (interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩)
        (interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩) := by
      refine ⟨?_, ?_⟩
      · rw [hθ_def]
      · rw [hθ_def]
        exact le_of_lt hstep_lt
    have hθ_ne : θ ≠ shiftedSortedAngleAt points hne s jj := by
      rw [hθ_def]
      exact ne_of_lt (interEventAngleAt_lt_shiftedSortedAngle_mod_pi (points := points)
        hne θ₀ s hafter hhigh jj)
    exact (only_event_between_interEventAnglesAt_mod_pi
      (L := L) (hne := hne) (θ₀ := θ₀) (s := s)
      (hlow := hlow) (hbefore := hbefore) (hafter := hafter)
      (hhigh := hhigh) (j := jj) a b hpq hθ_icc hθ_ne) hlevel

 theorem mono_at_eventAt_mod_pi {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi)
    (j : Fin (directionsDeterminedBy points).card) :
    Monotone (fun i => orientedLevel (shiftedSortedAngleAt points hne s j)
      ((sweepLabelingAt (points := points) hcard θ₀).point
        (sweepSort (sweepLabelingAt (points := points) hcard θ₀)
          (interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩) i))) := by
  apply sweepSort_event_level_monotone
  · exact inj_at_interEventAngleAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh
      ⟨j.val, by omega⟩
  · exact le_of_lt (interEventAngleAt_lt_shiftedSortedAngle_mod_pi (points := points)
      hne θ₀ s hafter hhigh j)
  · intro a b hab θ hθ
    have hθ_icc : θ ∈ Set.Icc
        (interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩)
        (interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩) := by
      rcases hθ with ⟨hlo, hhi⟩
      have hmid : shiftedSortedAngleAt points hne s j <
          interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩ :=
        shiftedSortedAngleAt_lt_interEventAngleAt_succ_mod_pi (points := points)
          hne θ₀ s hlow hbefore j
      exact ⟨le_of_lt hlo, le_trans (le_of_lt hhi) (le_of_lt hmid)⟩
    have hθ_ne : θ ≠ shiftedSortedAngleAt points hne s j := by
      rcases hθ with ⟨_hlo, hhi⟩
      exact ne_of_lt hhi
    exact only_event_between_interEventAnglesAt_mod_pi
      (L := sweepLabelingAt (points := points) hcard θ₀)
      (hne := hne) (θ₀ := θ₀) (s := s)
      (hlow := hlow) (hbefore := hbefore) (hafter := hafter)
      (hhigh := hhigh) (j := j) a b
      (fun h => hab ((sweepLabelingAt (points := points) hcard θ₀).point_injective h))
      hθ_icc hθ_ne

 theorem interEventAngleAt_span_mod_pi {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi)
    (j : Fin (directionsDeterminedBy points).card) :
    interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩ -
      interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩ < Real.pi := by
  have htop := interEventAngleAt_le_start_add_pi_mod_pi (points := points)
    hne θ₀ s hlow hbefore hafter hhigh ⟨j.val + 1, by omega⟩
  have hbot := startAngle_le_interEventAngleAt_mod_pi (points := points)
    hne θ₀ s hlow hbefore hafter hhigh ⟨j.val, by omega⟩
  by_cases hj0 : j.val = 0
  · have hj_succ_lt : j.val + 1 < (directionsDeterminedBy points).card := by omega
    have htop_strict :
        interEventAngleAt points hne θ₀ s ⟨j.val + 1, by omega⟩ < θ₀ + Real.pi := by
      exact lt_trans
        (interEventAngleAt_lt_shiftedSortedAngle_mod_pi (points := points)
          hne θ₀ s hafter hhigh ⟨j.val + 1, hj_succ_lt⟩)
        (shiftedSortedAngleAt_lt_start_add_pi_mod_pi (points := points)
          hne θ₀ s hlow hbefore ⟨j.val + 1, hj_succ_lt⟩)
    have hbot_eq :
        interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩ = θ₀ := by
      have hj : (⟨j.val, by omega⟩ :
          Fin ((directionsDeterminedBy points).card + 1)) =
          ⟨0, Nat.succ_pos _⟩ := Fin.ext hj0
      rw [hj, interEventAngleAt_zero]
    linarith
  · have hbot_strict :
        θ₀ < interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩ := by
      let jp : Fin (directionsDeterminedBy points).card := ⟨j.val - 1, by omega⟩
      have hprev :
          shiftedSortedAngleAt points hne s jp <
            interEventAngleAt points hne θ₀ s ⟨jp.val + 1, by omega⟩ :=
        shiftedSortedAngleAt_lt_interEventAngleAt_succ_mod_pi (points := points)
          hne θ₀ s hlow hbefore jp
      have hprev' :
          shiftedSortedAngleAt points hne s ⟨j.val - 1, by omega⟩ <
            interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩ := by
        have hj_prev : (⟨jp.val + 1, by omega⟩ :
            Fin ((directionsDeterminedBy points).card + 1)) =
            ⟨j.val, by omega⟩ := by
          apply Fin.ext
          simpa [jp] using Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hj0)
        simpa [jp, hj_prev] using hprev
      have hstart :
          θ₀ < shiftedSortedAngleAt points hne s ⟨j.val - 1, by omega⟩ :=
        shiftedSortedAngleAt_gt_start_mod_pi (points := points)
          hne θ₀ s hafter hhigh ⟨j.val - 1, by omega⟩
      exact lt_trans hstart hprev'
    linarith










 theorem shiftedSortedAngleAt_mod_pi_mem {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s j : Fin (directionsDeterminedBy points).card) :
    ∃ d ∈ directionsDeterminedBy points,
      shiftedSortedAngleAt points hne s j = d.angle ∨
      shiftedSortedAngleAt points hne s j = d.angle + Real.pi := by
  unfold shiftedSortedAngleAt
  set idx : Fin (directionsDeterminedBy points).card :=
    ⟨(s.val + j.val) % (directionsDeterminedBy points).card,
      Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩
  have hmem := sortedAngleAt_mem points idx
  rcases Finset.mem_image.mp hmem with ⟨d, hd, hangle⟩
  refine ⟨d, hd, ?_⟩
  by_cases hwrap : s.val + j.val < (directionsDeterminedBy points).card
  · left; simp [idx, hwrap, hangle]
  · right; simp [idx, hwrap, hangle]



 theorem nontrivial_blocks_at_eventAt_mod_pi {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (θ₀ : ℝ) (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi)
    (j : Fin (directionsDeterminedBy points).card) :
    (nontrivialLevelValues (fun i => orientedLevel (shiftedSortedAngleAt points hne s j)
      ((sweepLabelingAt (points := points) hcard θ₀).point
        (sweepSort (sweepLabelingAt (points := points) hcard θ₀)
          (interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩) i)))).Nonempty := by
  set L := sweepLabelingAt (points := points) hcard θ₀
  set g : Fin (2 * k) → ℝ := fun i => orientedLevel (shiftedSortedAngleAt points hne s j)
    (L.point (sweepSort L (interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩) i))
  set σ := sweepSort L (interEventAngleAt points hne θ₀ s ⟨j.val, by omega⟩)
  rcases shiftedSortedAngleAt_mod_pi_mem hne s j with ⟨d, hd, hangle_or⟩
  rcases (mem_directionsDeterminedBy_iff_exists_equal_level).mp hd with
    ⟨p, hp, q, hq, hpq_ne, hlevel⟩
  rcases L.point_surjective_on p hp with ⟨a, ha⟩
  rcases L.point_surjective_on q hq with ⟨b, hb⟩
  have hab : a ≠ b := fun h => hpq_ne (by rw [← ha, ← hb, h])
  have hdir_eq : direction p q = d := direction_eq_of_directionLevel_eq hpq_ne hlevel
  have htie_pq := orientedLevel_eq_at_direction_angle hpq_ne
  rw [hdir_eq] at htie_pq
  rcases hangle_or with hangle | hangle
  · have htie : g (σ.symm a) = g (σ.symm b) := by
      show orientedLevel _ (L.point (σ (σ.symm a))) =
        orientedLevel _ (L.point (σ (σ.symm b)))
      simp only [Equiv.apply_symm_apply, ha, hb, hangle]
      exact htie_pq
    have hii' : σ.symm a ≠ σ.symm b := fun h => hab (σ.symm.injective h)
    rcases lt_or_gt_of_ne hii' with h | h
    · have hhi_ge : σ.symm b ≤ levelBlockHi g (σ.symm a) :=
        le_levelBlockHi_of_monotone_eq'
          (mono_at_eventAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh j)
          htie.symm
      have hlt : (levelBlockLo g (σ.symm a)).val < (levelBlockHi g (σ.symm a)).val :=
        lt_of_le_of_lt (Fin.le_def.mp (levelBlockLo_le (f := g)))
          (lt_of_lt_of_le h (Fin.le_def.mp hhi_ge))
      exact ⟨g (σ.symm a), mem_nontrivialLevelValues_of_nontrivial_block hlt⟩
    · have hhi_ge : σ.symm a ≤ levelBlockHi g (σ.symm b) :=
        le_levelBlockHi_of_monotone_eq'
          (mono_at_eventAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh j)
          htie
      have hlt : (levelBlockLo g (σ.symm b)).val < (levelBlockHi g (σ.symm b)).val :=
        lt_of_le_of_lt (Fin.le_def.mp (levelBlockLo_le (f := g)))
          (lt_of_lt_of_le h (Fin.le_def.mp hhi_ge))
      exact ⟨g (σ.symm b), mem_nontrivialLevelValues_of_nontrivial_block hlt⟩
  · have h_add_pi_a :
        orientedLevel (d.angle + Real.pi) (L.point a) =
          -orientedLevel (d.angle) (L.point a) :=
      orientedLevel_add_pi (d.angle) (L.point a)
    have h_add_pi_b :
        orientedLevel (d.angle + Real.pi) (L.point b) =
          -orientedLevel (d.angle) (L.point b) :=
      orientedLevel_add_pi (d.angle) (L.point b)
    have htie_shifted :
        orientedLevel (shiftedSortedAngleAt points hne s j) (L.point a) =
          orientedLevel (shiftedSortedAngleAt points hne s j) (L.point b) := by
      rw [hangle, h_add_pi_a, h_add_pi_b, ha, hb, htie_pq]
    have htie : g (σ.symm a) = g (σ.symm b) := by
      show orientedLevel _ (L.point (σ (σ.symm a))) =
        orientedLevel _ (L.point (σ (σ.symm b)))
      simp only [Equiv.apply_symm_apply]
      exact htie_shifted
    have hii' : σ.symm a ≠ σ.symm b := fun h => hab (σ.symm.injective h)
    rcases lt_or_gt_of_ne hii' with h | h
    · have hhi_ge : σ.symm b ≤ levelBlockHi g (σ.symm a) :=
        le_levelBlockHi_of_monotone_eq'
          (mono_at_eventAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh j)
          htie.symm
      have hlt : (levelBlockLo g (σ.symm a)).val < (levelBlockHi g (σ.symm a)).val :=
        lt_of_le_of_lt (Fin.le_def.mp (levelBlockLo_le (f := g)))
          (lt_of_lt_of_le h (Fin.le_def.mp hhi_ge))
      exact ⟨g (σ.symm a), mem_nontrivialLevelValues_of_nontrivial_block hlt⟩
    · have hhi_ge : σ.symm a ≤ levelBlockHi g (σ.symm b) :=
        le_levelBlockHi_of_monotone_eq'
          (mono_at_eventAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh j)
          htie
      have hlt : (levelBlockLo g (σ.symm b)).val < (levelBlockHi g (σ.symm b)).val :=
        lt_of_le_of_lt (Fin.le_def.mp (levelBlockLo_le (f := g)))
          (lt_of_lt_of_le h (Fin.le_def.mp hhi_ge))
      exact ⟨g (σ.symm b), mem_nontrivialLevelValues_of_nontrivial_block hlt⟩

noncomputable def sweepConcreteGAS_at_mod_pi {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (θ₀ : ℝ)
    (s : Fin (directionsDeterminedBy points).card)
    (hlow : ∀ d ∈ directionsDeterminedBy points, d.angle - Real.pi < θ₀)
    (hbefore : ∀ t : Fin (directionsDeterminedBy points).card,
      t.val < s.val → sortedAngleAt points t < θ₀)
    (hafter : ∀ t : Fin (directionsDeterminedBy points).card,
      s.val ≤ t.val → θ₀ < sortedAngleAt points t)
    (hhigh : ∀ d ∈ directionsDeterminedBy points, θ₀ < d.angle + Real.pi)
    (hne_angle : ∀ d ∈ directionsDeterminedBy points, θ₀ ≠ d.angle) :
    ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy points).card := by
  set L := sweepLabelingAt (points := points) hcard θ₀
  set A := sweepGAS_at_mod_pi hcard hne θ₀ s hlow hhigh hne_angle hncoll
  let step : ∀ j : Fin (directionsDeterminedBy points).card,
      ReversalStep k (A.π (stepFrom j)) (A.π (stepTo j)) :=
    fun j => sweepReversalStep L
      (sweepLabelingAt_inj_mod_pi hcard θ₀ hlow hhigh hne_angle)
      (inj_at_interEventAngleAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh
        ⟨j.val, by omega⟩)
      (inj_at_interEventAngleAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh
        ⟨j.val + 1, by omega⟩)
      (sweepLabelingAt_id hcard hne θ₀)
      (interEventAngleAt_lt_shiftedSortedAngle_mod_pi (points := points)
        hne θ₀ s hafter hhigh j)
      (shiftedSortedAngleAt_lt_interEventAngleAt_succ_mod_pi (points := points)
        hne θ₀ s hlow hbefore j)
      (interEventAngleAt_span_mod_pi (points := points)
        hne hr θ₀ s hlow hbefore hafter hhigh j)
      (fun a b hab θ hθ hθ_ne =>
        only_event_between_interEventAnglesAt_mod_pi L hne θ₀ s hlow hbefore hafter hhigh
          j a b hab hθ hθ_ne)
      (fun a b hab htie θ hθ =>
        no_tie_from_start_to_interEventAt_mod_pi L hne θ₀ s hlow hbefore hafter hhigh
          j a b hab htie hθ)
      (startAngle_le_interEventAngleAt_mod_pi (points := points)
        hne θ₀ s hlow hbefore hafter hhigh (stepFrom j))
      (mono_at_eventAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh j)
      (nontrivial_blocks_at_eventAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh j)
  let hrev : ∀ j, (step j).move.ReversesBlocks :=
    fun j => @levelBlockMoveOfMonotone_reversesBlocks _ _
      (mono_at_eventAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh j)
      (nontrivial_blocks_at_eventAt_mod_pi hcard hne θ₀ s hlow hbefore hafter hhigh j)
  exact {
    toCountedGeneralizedAllowableSequence :=
      CountedGeneralizedAllowableSequence.ofReversesBlocks A step hrev
    reversesBlocks := hrev
  }

 theorem sortedAngleAt_lt_interEventAngle_of_lt_index {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    {s t : Fin (directionsDeterminedBy points).card}
    (ht : t.val < s.val) :
    sortedAngleAt points t <
      interEventAngle points hne ⟨s.val, by omega⟩ := by
  let sp : Fin (directionsDeterminedBy points).card := ⟨s.val - 1, by omega⟩
  have hprev :
      sortedAngleAt points sp <
        interEventAngle points hne ⟨sp.val + 1, by omega⟩ :=
    sortedAngle_lt_interEventAngle_succ hne sp
  have hprev' :
      sortedAngleAt points ⟨s.val - 1, by omega⟩ <
        interEventAngle points hne ⟨s.val, by omega⟩ := by
    have hfin : (⟨sp.val + 1, by omega⟩ :
        Fin ((directionsDeterminedBy points).card + 1)) =
        ⟨s.val, by omega⟩ := by
      apply Fin.ext
      simpa [sp] using Nat.succ_pred_eq_of_pos (by omega : 0 < s.val)
    simpa [sp, hfin] using hprev
  have ht_le_sp : t ≤ (⟨s.val - 1, by omega⟩ :
      Fin (directionsDeterminedBy points).card) := by
    change t.val ≤ s.val - 1
    omega
  have hle := (sortedAngleAt_strictMono points).monotone ht_le_sp
  exact lt_of_le_of_lt hle hprev'

 theorem interEventAngle_lt_sortedAngleAt_of_le_index {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    {s t : Fin (directionsDeterminedBy points).card}
    (hst : s.val ≤ t.val) :
    interEventAngle points hne ⟨s.val, by omega⟩ <
      sortedAngleAt points t := by
  have hs :
      interEventAngle points hne ⟨s.val, by omega⟩ <
        sortedAngleAt points s :=
    interEventAngle_lt_sortedAngle hne s
  have hle : sortedAngleAt points s ≤ sortedAngleAt points t :=
    (sortedAngleAt_strictMono points).monotone (Fin.le_def.mpr hst)
  exact lt_of_lt_of_le hs hle

 theorem direction_angle_sub_pi_lt_interEventAngle_index {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s : Fin (directionsDeterminedBy points).card)
    (d : Direction) (hd : d ∈ directionsDeterminedBy points) :
    d.angle - Real.pi < interEventAngle points hne ⟨s.val, by omega⟩ := by
  have hstart :=
    sweepStartAngle_le_interEventAngle hne ⟨s.val, by omega⟩
  have hlow := sweepStartAngle_gt_max_sub_pi points hne d hd
  linarith

 theorem interEventAngle_lt_direction_angle_add_pi_index {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s : Fin (directionsDeterminedBy points).card)
    (d : Direction) (_hd : d ∈ directionsDeterminedBy points) :
    interEventAngle points hne ⟨s.val, by omega⟩ < d.angle + Real.pi := by
  have hθ_lt_pi :
      interEventAngle points hne ⟨s.val, by omega⟩ < Real.pi :=
    lt_trans (interEventAngle_lt_sortedAngle hne s) (sortedAngleAt_lt_pi points s)
  have hd_nonneg : 0 ≤ d.angle := d.angle_nonneg
  linarith

 theorem interEventAngle_ne_direction_angle_index {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s : Fin (directionsDeterminedBy points).card)
    (d : Direction) (hd : d ∈ directionsDeterminedBy points) :
    interEventAngle points hne ⟨s.val, by omega⟩ ≠ d.angle := by
  intro heq
  rcases direction_angle_eq_sortedAngleAt d hd with ⟨idx, hangle⟩
  by_cases hlt : idx.val < s.val
  · have hbefore :=
      sortedAngleAt_lt_interEventAngle_of_lt_index (points := points) hne
        (s := s) (t := idx) hlt
    linarith
  · have hafter :=
      interEventAngle_lt_sortedAngleAt_of_le_index (points := points) hne
        (s := s) (t := idx) (by omega)
    linarith

noncomputable def sweepConcreteGAS_atIndex_mod_pi {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s : Fin (directionsDeterminedBy points).card) :
    ConcreteGeneralizedAllowableSequence k (directionsDeterminedBy points).card :=
  sweepConcreteGAS_at_mod_pi hcard hne hr hncoll
    (interEventAngle points hne ⟨s.val, by omega⟩) s
    (fun d hd => direction_angle_sub_pi_lt_interEventAngle_index hne s d hd)
    (fun t ht => sortedAngleAt_lt_interEventAngle_of_lt_index hne (s := s) (t := t) ht)
    (fun t ht => interEventAngle_lt_sortedAngleAt_of_le_index hne (s := s) (t := t) ht)
    (fun d hd => interEventAngle_lt_direction_angle_add_pi_index hne s d hd)
    (fun d hd => interEventAngle_ne_direction_angle_index hne s d hd)

theorem sweepLabelingAt_interEventAngle_point_eq {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (s : Fin (directionsDeterminedBy points).card)
    (a : Fin (2 * k)) :
    (sweepLabelingAt (points := points) hcard
      (interEventAngle points hne ⟨s.val, by omega⟩)).point a =
      ((sweepLabeling hcard hne).reindex
        (sweepSort (sweepLabeling hcard hne)
          (interEventAngle points hne ⟨s.val, by omega⟩))).point a := by
  let B := PointLabeling.ofCard hcard
  let θ := interEventAngle points hne ⟨s.val, by omega⟩
  let τ0 := sweepSort B (sweepStartAngle points hne)
  have hinjB : Function.Injective (fun x : Fin (2 * k) => orientedLevel θ (B.point x)) := by
    have hinjL := inj_at_interEventAngle hcard hne ⟨s.val, by omega⟩
    intro x y hxy
    have hxyL :
        orientedLevel θ ((B.reindex τ0).point (τ0.symm x)) =
          orientedLevel θ ((B.reindex τ0).point (τ0.symm y)) := by
      simp [PointLabeling.reindex, Function.comp, τ0, hxy]
    have hidx : τ0.symm x = τ0.symm y := by
      simpa [sweepLabeling, B, τ0, θ] using hinjL hxyL
    exact τ0.symm.injective hidx
  have hsort :
      sweepSort (B.reindex τ0) θ = (sweepSort B θ).trans τ0.symm :=
    sweepSort_reindex_of_injective B τ0 hinjB
  change B.point ((sweepSort B θ) a) =
    B.point (τ0 ((sweepSort (B.reindex τ0) θ) a))
  rw [hsort]
  simp [Equiv.trans_apply]

 theorem shiftedSortedAngleAt_unwrapped {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : s.val + j.val < (directionsDeterminedBy points).card) :
    shiftedSortedAngleAt points hne s j =
      sortedAngleAt points ⟨s.val + j.val, hwrap⟩ := by
  let r : ℕ := (directionsDeterminedBy points).card
  have hmod : (s.val + j.val) % r = s.val + j.val := by
    exact Nat.mod_eq_of_lt (by simpa [r] using hwrap)
  have hfin :
      (⟨(s.val + j.val) % (directionsDeterminedBy points).card,
        Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩ :
          Fin (directionsDeterminedBy points).card) =
        ⟨s.val + j.val, hwrap⟩ := by
    apply Fin.ext
    simpa [r] using hmod
  simp [shiftedSortedAngleAt, hwrap, hfin]

 theorem shiftedSortedAngleAt_wrapped {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : ¬ s.val + j.val < (directionsDeterminedBy points).card) :
    shiftedSortedAngleAt points hne s j =
      sortedAngleAt points
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by
          omega⟩ + Real.pi := by
  let r : ℕ := (directionsDeterminedBy points).card
  have hge : r ≤ s.val + j.val := by
    simpa [r] using (by omega :
      (directionsDeterminedBy points).card ≤ s.val + j.val)
  have hlt_sub : s.val + j.val - r < r := by omega
  have hmod : (s.val + j.val) % r = s.val + j.val - r := by
    rw [Nat.mod_eq_sub_mod hge]
    exact Nat.mod_eq_of_lt hlt_sub
  have hfin :
      (⟨(s.val + j.val) % (directionsDeterminedBy points).card,
        Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩ :
          Fin (directionsDeterminedBy points).card) =
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by
          simpa [r] using hlt_sub⟩ := by
    apply Fin.ext
    simpa [r] using hmod
  simp [shiftedSortedAngleAt, hwrap, hfin]

 theorem interEventAngleAt_unwrapped {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : s.val + j.val < (directionsDeterminedBy points).card) :
    interEventAngleAt points hne
        (interEventAngle points hne ⟨s.val, by omega⟩) s
        ⟨j.val, by omega⟩ =
      interEventAngle points hne ⟨s.val + j.val, by omega⟩ := by
  by_cases hj0 : j.val = 0
  · have hj : (⟨j.val, by omega⟩ :
        Fin ((directionsDeterminedBy points).card + 1)) =
        ⟨0, Nat.succ_pos _⟩ := Fin.ext hj0
    have hsj : (⟨s.val + j.val, by omega⟩ :
        Fin ((directionsDeterminedBy points).card + 1)) =
        ⟨s.val, by omega⟩ := by
      apply Fin.ext
      simp [hj0]
    rw [hj, interEventAngleAt_zero, hsj]
  · let jprev : Fin (directionsDeterminedBy points).card := ⟨j.val - 1, by omega⟩
    have hj_not_last : j.val ≠ (directionsDeterminedBy points).card := by omega
    have hsum_ne_last :
        s.val + j.val ≠ (directionsDeterminedBy points).card := by omega
    have hwrap_prev : s.val + jprev.val < (directionsDeterminedBy points).card := by
      dsimp [jprev]
      omega
    have hprev :
        shiftedSortedAngleAt points hne s jprev =
          sortedAngleAt points ⟨s.val + j.val - 1, by omega⟩ := by
      have hprev0 := shiftedSortedAngleAt_unwrapped (points := points) hne s jprev hwrap_prev
      have hidx : (⟨s.val + jprev.val, hwrap_prev⟩ :
          Fin (directionsDeterminedBy points).card) =
          ⟨s.val + j.val - 1, by omega⟩ := by
        apply Fin.ext
        dsimp [jprev]
        omega
      simpa [hidx] using hprev0
    have hcur :
        shiftedSortedAngleAt points hne s j =
          sortedAngleAt points ⟨s.val + j.val, hwrap⟩ :=
      shiftedSortedAngleAt_unwrapped (points := points) hne s j hwrap
    simp [interEventAngleAt, interEventAngle, hj0, hj_not_last,
      hsum_ne_last, jprev, hprev, hcur]

 theorem interEventAngleAt_wrapped_nonzero {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : (directionsDeterminedBy points).card < s.val + j.val) :
    interEventAngleAt points hne
        (interEventAngle points hne ⟨s.val, by omega⟩) s
        ⟨j.val, by omega⟩ =
      interEventAngle points hne
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ +
          Real.pi := by
  let r : ℕ := (directionsDeterminedBy points).card
  have hr : 0 < r := by simpa [r] using Finset.card_pos.mpr hne
  have hj0 : j.val ≠ 0 := by omega
  have hj_not_last : j.val ≠ (directionsDeterminedBy points).card := by
    omega
  let jprev : Fin (directionsDeterminedBy points).card := ⟨j.val - 1, by omega⟩
  have hwrap_prev : ¬ s.val + jprev.val < (directionsDeterminedBy points).card := by
    dsimp [jprev]
    omega
  have hprev :
      shiftedSortedAngleAt points hne s jprev =
        sortedAngleAt points
          ⟨s.val + j.val - (directionsDeterminedBy points).card - 1, by omega⟩ +
            Real.pi := by
    have hprev0 := shiftedSortedAngleAt_wrapped (points := points) hne s jprev hwrap_prev
    have hidx :
        (⟨s.val + jprev.val - (directionsDeterminedBy points).card, by
          have hr' : 0 < (directionsDeterminedBy points).card := Finset.card_pos.mpr hne
          have hs' := s.isLt
          have hj' := jprev.isLt
          omega⟩ : Fin (directionsDeterminedBy points).card) =
          ⟨s.val + j.val - (directionsDeterminedBy points).card - 1, by omega⟩ := by
      apply Fin.ext
      dsimp [jprev]
      omega
    simpa [hidx] using hprev0
  have hcur :
      shiftedSortedAngleAt points hne s j =
        sortedAngleAt points
          ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ +
            Real.pi := by
    exact shiftedSortedAngleAt_wrapped (points := points) hne s j (by omega)
  have htarget_nonzero :
      s.val + j.val - (directionsDeterminedBy points).card ≠ 0 := by
    omega
  have htarget_not_last :
      s.val + j.val - (directionsDeterminedBy points).card ≠
        (directionsDeterminedBy points).card := by
    omega
  simp [interEventAngleAt, interEventAngle, hj0, hj_not_last,
    htarget_nonzero, htarget_not_last, jprev, hprev, hcur,
    genericAngleBetween_add_pi]

 theorem genericAngleBetween_last_first_add_pi_eq_start_add_pi
    {points : Finset Point2} (hne : (directionsDeterminedBy points).Nonempty) :
    genericAngleBetween
      (sortedAngleAt points ⟨(directionsDeterminedBy points).card - 1,
        Nat.sub_lt (Finset.card_pos.mpr hne) Nat.zero_lt_one⟩)
      (sortedAngleAt points ⟨0, Finset.card_pos.mpr hne⟩ + Real.pi) =
        sweepStartAngle points hne + Real.pi := by
  let angles := (directionsDeterminedBy points).image Direction.angle
  have hzero : sortedAngleAt points ⟨0, Finset.card_pos.mpr hne⟩ =
      angles.min' (Finset.Nonempty.image hne Direction.angle) := by
    unfold sortedAngleAt sortedDirectionAngles
    simpa [angles] using (Finset.sorted_zero_eq_min' (s := angles)
      (h := by
        simpa [angles, Finset.length_sort,
          Finset.card_image_of_injective _ Direction.angle_injective] using
          Finset.card_pos.mpr hne))
  have hlast :
      sortedAngleAt points
          ⟨(directionsDeterminedBy points).card - 1,
            Nat.sub_lt (Finset.card_pos.mpr hne) Nat.zero_lt_one⟩ =
        angles.max' (Finset.Nonempty.image hne Direction.angle) := by
    unfold sortedAngleAt sortedDirectionAngles
    simpa [angles, Finset.length_sort,
      Finset.card_image_of_injective _ Direction.angle_injective] using
      (Finset.sorted_last_eq_max' (s := angles)
        (h := by
          simpa [angles, Finset.length_sort,
            Finset.card_image_of_injective _ Direction.angle_injective] using
            Nat.sub_lt (Finset.card_pos.mpr hne) Nat.zero_lt_one))
  unfold genericAngleBetween sweepStartAngle
  simp [angles, hzero, hlast]
  ring

theorem interEventAngleAt_wrapped {points : Finset Point2}
    (hne : (directionsDeterminedBy points).Nonempty)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val) :
    interEventAngleAt points hne
        (interEventAngle points hne ⟨s.val, by omega⟩) s
        ⟨j.val, by omega⟩ =
      interEventAngle points hne
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ + Real.pi := by
  by_cases hstrict : (directionsDeterminedBy points).card < s.val + j.val
  · exact interEventAngleAt_wrapped_nonzero hne s j hstrict
  · have heq : s.val + j.val = (directionsDeterminedBy points).card := by omega
    have hj0 : j.val ≠ 0 := by omega
    have hj_not_last : j.val ≠ (directionsDeterminedBy points).card := by
      exact ne_of_lt j.isLt
    let jprev : Fin (directionsDeterminedBy points).card := ⟨j.val - 1, by omega⟩
    have hwrap_prev : s.val + jprev.val < (directionsDeterminedBy points).card := by
      dsimp [jprev]
      omega
    have hprev :
        shiftedSortedAngleAt points hne s jprev =
          sortedAngleAt points
            ⟨(directionsDeterminedBy points).card - 1,
              Nat.sub_lt (Finset.card_pos.mpr hne) Nat.zero_lt_one⟩ := by
      have hprev0 := shiftedSortedAngleAt_unwrapped (points := points) hne s jprev hwrap_prev
      have hidx :
          (⟨s.val + jprev.val, hwrap_prev⟩ :
            Fin (directionsDeterminedBy points).card) =
          ⟨(directionsDeterminedBy points).card - 1,
            Nat.sub_lt (Finset.card_pos.mpr hne) Nat.zero_lt_one⟩ := by
        apply Fin.ext
        dsimp [jprev]
        omega
      simpa [hidx] using hprev0
    have hcur :
        shiftedSortedAngleAt points hne s j =
          sortedAngleAt points ⟨0, Finset.card_pos.mpr hne⟩ + Real.pi := by
      have hcur0 := shiftedSortedAngleAt_wrapped (points := points) hne s j (by omega)
      have hidx :
          (⟨s.val + j.val - (directionsDeterminedBy points).card, by
            have hr : 0 < (directionsDeterminedBy points).card := Finset.card_pos.mpr hne
            have hs := s.isLt
            have hj := j.isLt
            omega⟩ : Fin (directionsDeterminedBy points).card) =
          ⟨0, Finset.card_pos.mpr hne⟩ := by
        apply Fin.ext
        change s.val + j.val - (directionsDeterminedBy points).card = 0
        omega
      simpa [hidx] using hcur0
    have hrepr :
        interEventAngleAt points hne
            (interEventAngle points hne ⟨s.val, by omega⟩) s
            ⟨j.val, by omega⟩ =
          genericAngleBetween
            (sortedAngleAt points
              ⟨(directionsDeterminedBy points).card - 1,
                Nat.sub_lt (Finset.card_pos.mpr hne) Nat.zero_lt_one⟩)
            (sortedAngleAt points ⟨0, Finset.card_pos.mpr hne⟩ + Real.pi) := by
      simp [interEventAngleAt, hj0, hj_not_last, jprev, hprev, hcur]
    have htarget :
        (⟨s.val + j.val - (directionsDeterminedBy points).card, by
          have hs := s.isLt
          have hj := j.isLt
          omega⟩ : Fin ((directionsDeterminedBy points).card + 1)) =
          ⟨0, Nat.succ_pos _⟩ := by
      apply Fin.ext
      change s.val + j.val - (directionsDeterminedBy points).card = 0
      omega
    rw [hrepr, htarget, interEventAngle_zero]
    exact genericAngleBetween_last_first_add_pi_eq_start_add_pi hne





theorem sweepSort_labelingAt_interEventAngle_no_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : s.val + j.val < (directionsDeterminedBy points).card) :
    sweepSort
        (sweepLabelingAt (points := points) hcard
          (interEventAngle points hne ⟨s.val, by omega⟩))
        (interEventAngleAt points hne
          (interEventAngle points hne ⟨s.val, by omega⟩) s
          ⟨j.val, by omega⟩) =
      (sweepSort (sweepLabeling hcard hne)
        (interEventAngle points hne ⟨s.val + j.val, Nat.lt_succ_of_lt hwrap⟩)).trans
        (sweepSort (sweepLabeling hcard hne)
          (interEventAngle points hne ⟨s.val, by omega⟩)).symm := by
  let L := sweepLabeling hcard hne
  let θs := interEventAngle points hne ⟨s.val, by omega⟩
  let θjAt := interEventAngleAt points hne θs s ⟨j.val, by omega⟩
  have hfun :
      (fun a : Fin (2 * k) => orientedLevel θjAt
        ((sweepLabelingAt (points := points) hcard θs).point a)) =
      (fun a : Fin (2 * k) => orientedLevel θjAt
        ((L.reindex (sweepSort L θs)).point a)) := by
    funext a
    rw [sweepLabelingAt_interEventAngle_point_eq hcard hne s a]
  have hlabel :
      sweepSort (sweepLabelingAt (points := points) hcard θs) θjAt =
        sweepSort (L.reindex (sweepSort L θs)) θjAt := by
    show Tuple.sort (fun a : Fin (2 * k) =>
        orientedLevel θjAt
          ((sweepLabelingAt (points := points) hcard θs).point a)) =
      Tuple.sort (fun a : Fin (2 * k) =>
        orientedLevel θjAt ((L.reindex (sweepSort L θs)).point a))
    rw [hfun]
  have hangle :
      θjAt =
        interEventAngle points hne ⟨s.val + j.val, Nat.lt_succ_of_lt hwrap⟩ := by
    simpa [θjAt, θs] using interEventAngleAt_unwrapped (points := points) hne s j hwrap
  rw [hlabel, hangle]
  exact sweepSort_reindex_of_injective L (sweepSort L θs)
    (inj_at_interEventAngle hcard hne ⟨s.val + j.val, Nat.lt_succ_of_lt hwrap⟩)

 theorem inj_at_interEventAngle_add_pi {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (j : Fin ((directionsDeterminedBy points).card + 1)) :
    Function.Injective (fun a : Fin (2 * k) =>
      orientedLevel (interEventAngle points hne j + Real.pi)
        ((sweepLabeling hcard hne).point a)) := by
  intro a b hab
  apply inj_at_interEventAngle hcard hne j
  have ha := orientedLevel_add_pi (interEventAngle points hne j)
    ((sweepLabeling hcard hne).point a)
  have hb := orientedLevel_add_pi (interEventAngle points hne j)
    ((sweepLabeling hcard hne).point b)
  linarith

theorem sweepSort_labelingAt_interEventAngle_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val) :
    sweepSort
        (sweepLabelingAt (points := points) hcard
          (interEventAngle points hne ⟨s.val, by omega⟩))
        (interEventAngleAt points hne
          (interEventAngle points hne ⟨s.val, by omega⟩) s
          ⟨j.val, by omega⟩) =
      (sweepSort (sweepLabeling hcard hne)
        (interEventAngle points hne
          ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ +
            Real.pi)).trans
        (sweepSort (sweepLabeling hcard hne)
          (interEventAngle points hne ⟨s.val, by omega⟩)).symm := by
  let L := sweepLabeling hcard hne
  let θs := interEventAngle points hne ⟨s.val, by omega⟩
  let θjAt := interEventAngleAt points hne θs s ⟨j.val, by omega⟩
  let t : Fin ((directionsDeterminedBy points).card + 1) :=
    ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩
  have hfun :
      (fun a : Fin (2 * k) => orientedLevel θjAt
        ((sweepLabelingAt (points := points) hcard θs).point a)) =
      (fun a : Fin (2 * k) => orientedLevel θjAt
        ((L.reindex (sweepSort L θs)).point a)) := by
    funext a
    rw [sweepLabelingAt_interEventAngle_point_eq hcard hne s a]
  have hlabel :
      sweepSort (sweepLabelingAt (points := points) hcard θs) θjAt =
        sweepSort (L.reindex (sweepSort L θs)) θjAt := by
    show Tuple.sort (fun a : Fin (2 * k) =>
        orientedLevel θjAt
          ((sweepLabelingAt (points := points) hcard θs).point a)) =
      Tuple.sort (fun a : Fin (2 * k) =>
        orientedLevel θjAt ((L.reindex (sweepSort L θs)).point a))
    rw [hfun]
  have hangle :
      θjAt = interEventAngle points hne t + Real.pi := by
    simpa [θjAt, θs, t] using interEventAngleAt_wrapped
      (points := points) hne s j hwrap
  rw [hlabel, hangle]
  exact sweepSort_reindex_of_injective L (sweepSort L θs)
    (inj_at_interEventAngle_add_pi hcard hne t)

theorem sweepSort_labelingAt_interEventAngle_wrap_rev
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val) :
    sweepSort
        (sweepLabelingAt (points := points) hcard
          (interEventAngle points hne ⟨s.val, by omega⟩))
        (interEventAngleAt points hne
          (interEventAngle points hne ⟨s.val, by omega⟩) s
          ⟨j.val, by omega⟩) =
      ((Fin.revPerm : Equiv.Perm (Fin (2 * k))).trans
        (sweepSort (sweepLabeling hcard hne)
          (interEventAngle points hne
            ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩))).trans
        (sweepSort (sweepLabeling hcard hne)
          (interEventAngle points hne ⟨s.val, by omega⟩)).symm := by
  let t : Fin ((directionsDeterminedBy points).card + 1) :=
    ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩
  rw [sweepSort_labelingAt_interEventAngle_wrap hcard hne s j hwrap]
  rw [show (interEventAngle points hne
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩) =
      interEventAngle points hne t by rfl]
  rw [sweepSort_add_pi_eq_revPerm_trans (sweepLabeling hcard hne)
    (interEventAngle points hne t) (inj_at_interEventAngle hcard hne t)]

theorem sweepConcreteGAS_atIndex_mod_pi_seq_no_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : s.val + j.val < (directionsDeterminedBy points).card) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π
        ⟨j.val, by omega⟩ =
      (sweepSort (sweepLabeling hcard hne)
        (interEventAngle points hne ⟨s.val + j.val, Nat.lt_succ_of_lt hwrap⟩)).trans
        (sweepSort (sweepLabeling hcard hne)
          (interEventAngle points hne ⟨s.val, by omega⟩)).symm := by
  simpa [sweepConcreteGAS_atIndex_mod_pi, sweepConcreteGAS_at_mod_pi,
    CountedGeneralizedAllowableSequence.ofReversesBlocks,
    sweepGAS_at_mod_pi, GeneralizedAllowableSequence.ofSweepAngles] using
    sweepSort_labelingAt_interEventAngle_no_wrap hcard hne s j hwrap



theorem sweepConcreteGAS_atIndex_mod_pi_seq_wrap_rev
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π
        ⟨j.val, by omega⟩ =
      ((Fin.revPerm : Equiv.Perm (Fin (2 * k))).trans
        (sweepSort (sweepLabeling hcard hne)
          (interEventAngle points hne
            ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩))).trans
        (sweepSort (sweepLabeling hcard hne)
          (interEventAngle points hne ⟨s.val, by omega⟩)).symm := by
  simpa [sweepConcreteGAS_atIndex_mod_pi, sweepConcreteGAS_at_mod_pi,
    CountedGeneralizedAllowableSequence.ofReversesBlocks,
    sweepGAS_at_mod_pi, GeneralizedAllowableSequence.ofSweepAngles] using
    sweepSort_labelingAt_interEventAngle_wrap_rev hcard hne s j hwrap

theorem sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : s.val + j.val + 1 < (directionsDeterminedBy points).card) :
    GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq j =
      GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS hcard hne hr hncoll).seq
          ⟨s.val + j.val, by omega⟩ := by
  let L := sweepLabeling hcard hne
  let θs := interEventAngle points hne ⟨s.val, by omega⟩
  let τ := sweepSort L θs
  let l : Fin (directionsDeterminedBy points).card := ⟨s.val + j.val, by omega⟩
  let jnext : Fin (directionsDeterminedBy points).card := ⟨j.val + 1, by omega⟩
  have hB0 := sweepConcreteGAS_atIndex_mod_pi_seq_no_wrap
    hcard hne hr hncoll s j (by omega : s.val + j.val < (directionsDeterminedBy points).card)
  have hB1 := sweepConcreteGAS_atIndex_mod_pi_seq_no_wrap
    hcard hne hr hncoll s jnext (by
      dsimp [jnext]
      omega)
  have hA0 : (sweepConcreteGAS hcard hne hr hncoll).seq.π (stepFrom l) =
      sweepSort L (interEventAngle points hne ⟨s.val + j.val, by omega⟩) := by
    simp [sweepConcreteGAS, CountedGeneralizedAllowableSequence.ofReversesBlocks,
      sweepGAS, GeneralizedAllowableSequence.ofSweepAngles, stepFrom, L, l]
  have hA1 : (sweepConcreteGAS hcard hne hr hncoll).seq.π (stepTo l) =
      sweepSort L (interEventAngle points hne ⟨s.val + j.val + 1, by omega⟩) := by
    simp [sweepConcreteGAS, CountedGeneralizedAllowableSequence.ofReversesBlocks,
      sweepGAS, GeneralizedAllowableSequence.ofSweepAngles, stepTo, L, l]
  change stepCrossingLabelsCard k
      ((sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π (stepFrom j))
      ((sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π (stepTo j)) =
    stepCrossingLabelsCard k
      ((sweepConcreteGAS hcard hne hr hncoll).seq.π (stepFrom l))
      ((sweepConcreteGAS hcard hne hr hncoll).seq.π (stepTo l))
  dsimp [stepFrom, stepTo] at hB0 hB1 hA0 hA1 ⊢
  rw [hB0, hB1, hA0, hA1]
  change stepCrossingLabelsCard k
      ((sweepSort L (interEventAngle points hne ⟨s.val + j.val, by omega⟩)).trans τ.symm)
      ((sweepSort L (interEventAngle points hne ⟨s.val + j.val + 1, by omega⟩)).trans τ.symm) =
    stepCrossingLabelsCard k
      (sweepSort L (interEventAngle points hne ⟨s.val + j.val, by omega⟩))
      (sweepSort L (interEventAngle points hne ⟨s.val + j.val + 1, by omega⟩))
  exact stepCrossingLabelsCard_relabel _ _ τ

theorem sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap_to_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hsource : s.val + j.val < (directionsDeterminedBy points).card)
    (hboundary : s.val + j.val + 1 = (directionsDeterminedBy points).card)
    (hnext : j.val + 1 < (directionsDeterminedBy points).card) :
    GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq j =
      GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS hcard hne hr hncoll).seq
          ⟨s.val + j.val, hsource⟩ := by
  let L := sweepLabeling hcard hne
  let θs := interEventAngle points hne ⟨s.val, by omega⟩
  let τ := sweepSort L θs
  let l : Fin (directionsDeterminedBy points).card := ⟨s.val + j.val, hsource⟩
  let jnext : Fin (directionsDeterminedBy points).card := ⟨j.val + 1, hnext⟩
  have hwrap_next :
      (directionsDeterminedBy points).card ≤ s.val + jnext.val := by
    dsimp [jnext]
    omega
  have hB0 := sweepConcreteGAS_atIndex_mod_pi_seq_no_wrap
    hcard hne hr hncoll s j hsource
  have hB1 := sweepConcreteGAS_atIndex_mod_pi_seq_wrap_rev
    hcard hne hr hncoll s jnext hwrap_next
  have hB1' :
      (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π (stepTo j) =
        (((Fin.revPerm : Equiv.Perm (Fin (2 * k))).trans
          (sweepSort L (interEventAngle points hne ⟨0, Nat.succ_pos _⟩))).trans
          τ.symm) := by
    have hidx :
        (⟨s.val + jnext.val - (directionsDeterminedBy points).card, by omega⟩ :
          Fin ((directionsDeterminedBy points).card + 1)) =
          ⟨0, Nat.succ_pos _⟩ := by
      apply Fin.ext
      dsimp [jnext]
      omega
    dsimp [stepTo] at hB1 ⊢
    simpa [L, τ, hidx] using hB1
  have hA0 : (sweepConcreteGAS hcard hne hr hncoll).seq.π (stepFrom l) =
      sweepSort L (interEventAngle points hne ⟨s.val + j.val, by omega⟩) := by
    simp [sweepConcreteGAS, CountedGeneralizedAllowableSequence.ofReversesBlocks,
      sweepGAS, GeneralizedAllowableSequence.ofSweepAngles, stepFrom, L, l]
  have hA1 : (sweepConcreteGAS hcard hne hr hncoll).seq.π (stepTo l) =
      reverseFin (2 * k) := by
    have hidx : (stepTo l : Fin ((directionsDeterminedBy points).card + 1)) =
        ⟨(directionsDeterminedBy points).card, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp [stepTo, l]
      exact hboundary
    rw [hidx]
    exact (sweepConcreteGAS hcard hne hr hncoll).seq.finish
  have hsort0 :
      sweepSort L (interEventAngle points hne ⟨0, Nat.succ_pos _⟩) =
        Equiv.refl (Fin (2 * k)) := by
    simpa [sweepConcreteGAS, CountedGeneralizedAllowableSequence.ofReversesBlocks,
      sweepGAS, GeneralizedAllowableSequence.ofSweepAngles, L] using
      (sweepConcreteGAS hcard hne hr hncoll).seq.start
  have hsort0_ofNat :
      sweepSort L (interEventAngle points hne
          (0 : Fin ((directionsDeterminedBy points).card + 1))) =
        Equiv.refl (Fin (2 * k)) := by
    simpa using hsort0
  change stepCrossingLabelsCard k
      ((sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π (stepFrom j))
      ((sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π (stepTo j)) =
    stepCrossingLabelsCard k
      ((sweepConcreteGAS hcard hne hr hncoll).seq.π (stepFrom l))
      ((sweepConcreteGAS hcard hne hr hncoll).seq.π (stepTo l))
  dsimp [stepFrom, stepTo] at hB0 hB1' hA0 hA1 ⊢
  rw [hB0, hB1', hA0, hA1, hsort0_ofNat]
  change stepCrossingLabelsCard k
      ((sweepSort L (interEventAngle points hne ⟨s.val + j.val, by omega⟩)).trans τ.symm)
      ((reverseFin (2 * k)).trans τ.symm) =
    stepCrossingLabelsCard k
      (sweepSort L (interEventAngle points hne ⟨s.val + j.val, by omega⟩))
      (reverseFin (2 * k))
  exact stepCrossingLabelsCard_relabel _ _ τ

theorem sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap_nonlast
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val)
    (hnext : j.val + 1 < (directionsDeterminedBy points).card) :
    GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq j =
      GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS hcard hne hr hncoll).seq
          ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ := by
  let L := sweepLabeling hcard hne
  let θs := interEventAngle points hne ⟨s.val, by omega⟩
  let τ := sweepSort L θs
  let l : Fin (directionsDeterminedBy points).card :=
    ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩
  let jnext : Fin (directionsDeterminedBy points).card := ⟨j.val + 1, hnext⟩
  have hwrap_next :
      (directionsDeterminedBy points).card ≤ s.val + jnext.val := by
    dsimp [jnext]
    omega
  have hB0 := sweepConcreteGAS_atIndex_mod_pi_seq_wrap_rev
    hcard hne hr hncoll s j hwrap
  have hB1 := sweepConcreteGAS_atIndex_mod_pi_seq_wrap_rev
    hcard hne hr hncoll s jnext hwrap_next
  have hA0 : (sweepConcreteGAS hcard hne hr hncoll).seq.π (stepFrom l) =
      sweepSort L (interEventAngle points hne
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩) := by
    simp [sweepConcreteGAS, CountedGeneralizedAllowableSequence.ofReversesBlocks,
      sweepGAS, GeneralizedAllowableSequence.ofSweepAngles, stepFrom, L, l]
  have hA1 : (sweepConcreteGAS hcard hne hr hncoll).seq.π (stepTo l) =
      sweepSort L (interEventAngle points hne
        ⟨s.val + j.val + 1 - (directionsDeterminedBy points).card, by omega⟩) := by
    have hidx :
        (⟨s.val + j.val - (directionsDeterminedBy points).card + 1, by omega⟩ :
          Fin ((directionsDeterminedBy points).card + 1)) =
        ⟨s.val + j.val + 1 - (directionsDeterminedBy points).card, by omega⟩ := by
      apply Fin.ext
      simpa [Nat.succ_eq_add_one] using (Nat.succ_sub hwrap).symm
    simp [sweepConcreteGAS, CountedGeneralizedAllowableSequence.ofReversesBlocks,
      sweepGAS, GeneralizedAllowableSequence.ofSweepAngles, stepTo, L, l, hidx]
  change stepCrossingLabelsCard k
      ((sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π (stepFrom j))
      ((sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π (stepTo j)) =
    stepCrossingLabelsCard k
      ((sweepConcreteGAS hcard hne hr hncoll).seq.π (stepFrom l))
      ((sweepConcreteGAS hcard hne hr hncoll).seq.π (stepTo l))
  dsimp [stepFrom, stepTo] at hB0 hB1 hA0 hA1 ⊢
  rw [hB0, hB1, hA0, hA1]
  change stepCrossingLabelsCard k
      (((Fin.revPerm : Equiv.Perm (Fin (2 * k))).trans
        (sweepSort L (interEventAngle points hne
          ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩))).trans τ.symm)
      (((Fin.revPerm : Equiv.Perm (Fin (2 * k))).trans
        (sweepSort L (interEventAngle points hne
          ⟨s.val + j.val + 1 - (directionsDeterminedBy points).card, by omega⟩))).trans τ.symm) =
    stepCrossingLabelsCard k
      (sweepSort L (interEventAngle points hne
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩))
      (sweepSort L (interEventAngle points hne
        ⟨s.val + j.val + 1 - (directionsDeterminedBy points).card, by omega⟩))
  rw [stepCrossingLabelsCard_relabel]
  simpa [reverseFin_eq_revPerm] using
    stepCrossingLabelsCard_reverse_left
      (sweepSort L (interEventAngle points hne
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩))
      (sweepSort L (interEventAngle points hne
        ⟨s.val + j.val + 1 - (directionsDeterminedBy points).card, by omega⟩))

theorem sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap_last
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val)
    (hlast : j.val + 1 = (directionsDeterminedBy points).card) :
    GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq j =
      GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS hcard hne hr hncoll).seq
          ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ := by
  let L := sweepLabeling hcard hne
  let θs := interEventAngle points hne ⟨s.val, by omega⟩
  let τ := sweepSort L θs
  let l : Fin (directionsDeterminedBy points).card :=
    ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩
  have hB0 := sweepConcreteGAS_atIndex_mod_pi_seq_wrap_rev
    hcard hne hr hncoll s j hwrap
  have hB1 :
      (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π (stepTo j) =
        reverseFin (2 * k) := by
    have hidx : (stepTo j : Fin ((directionsDeterminedBy points).card + 1)) =
        ⟨(directionsDeterminedBy points).card, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      dsimp [stepTo]
      exact hlast
    rw [hidx]
    exact (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.finish
  have hA0 : (sweepConcreteGAS hcard hne hr hncoll).seq.π (stepFrom l) =
      sweepSort L (interEventAngle points hne
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩) := by
    simp [sweepConcreteGAS, CountedGeneralizedAllowableSequence.ofReversesBlocks,
      sweepGAS, GeneralizedAllowableSequence.ofSweepAngles, stepFrom, L, l]
  have hA1 : (sweepConcreteGAS hcard hne hr hncoll).seq.π (stepTo l) = τ := by
    have hidx :
        (⟨s.val + j.val - (directionsDeterminedBy points).card + 1, by omega⟩ :
          Fin ((directionsDeterminedBy points).card + 1)) =
        ⟨s.val, by omega⟩ := by
      apply Fin.ext
      change s.val + j.val - (directionsDeterminedBy points).card + 1 = s.val
      omega
    simp [sweepConcreteGAS, CountedGeneralizedAllowableSequence.ofReversesBlocks,
      sweepGAS, GeneralizedAllowableSequence.ofSweepAngles, stepTo, L, l, θs, τ, hidx]
  change stepCrossingLabelsCard k
      ((sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π (stepFrom j))
      ((sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq.π (stepTo j)) =
    stepCrossingLabelsCard k
      ((sweepConcreteGAS hcard hne hr hncoll).seq.π (stepFrom l))
      ((sweepConcreteGAS hcard hne hr hncoll).seq.π (stepTo l))
  dsimp [stepFrom, stepTo] at hB0 hB1 hA0 hA1 ⊢
  rw [hB0, hB1, hA0, hA1]
  have hrevτ : (((reverseFin (2 * k)).trans τ).trans τ.symm) = reverseFin (2 * k) := by
    ext a
    simp [reverseFin]
  rw [← hrevτ]
  simpa [reverseFin_eq_revPerm] using
    stepCrossingLabelsCard_reverse_left_relabel
      (sweepSort L (interEventAngle points hne
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩)) τ τ

theorem sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val) :
    GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq j =
      GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS hcard hne hr hncoll).seq
          ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ := by
  by_cases hlast : j.val + 1 = (directionsDeterminedBy points).card
  · exact sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap_last
      hcard hne hr hncoll s j hwrap hlast
  · exact sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap_nonlast
      hcard hne hr hncoll s j hwrap (by
        have hjle : j.val + 1 ≤ (directionsDeterminedBy points).card := j.isLt
        omega)







theorem sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_shifted_nonfinal
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hnext : j.val + 1 < (directionsDeterminedBy points).card) :
    GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).seq j =
      GeneralizedAllowableSequence.crossingLabelsCard
        (sweepConcreteGAS hcard hne hr hncoll).seq
          ⟨(s.val + j.val) % (directionsDeterminedBy points).card,
            Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩ := by
  by_cases hsource : s.val + j.val < (directionsDeterminedBy points).card
  · by_cases hstrict : s.val + j.val + 1 < (directionsDeterminedBy points).card
    · have h := sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap
        hcard hne hr hncoll s j hstrict
      have htarget :
          (⟨s.val + j.val, by omega⟩ : Fin (directionsDeterminedBy points).card) =
          ⟨(s.val + j.val) % (directionsDeterminedBy points).card,
            Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩ := by
        apply Fin.ext
        exact (Nat.mod_eq_of_lt hsource).symm
      simpa [htarget] using h
    · have hboundary : s.val + j.val + 1 = (directionsDeterminedBy points).card := by
        have hle : s.val + j.val + 1 ≤ (directionsDeterminedBy points).card := by omega
        omega
      have h := sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap_to_wrap
        hcard hne hr hncoll s j hsource hboundary hnext
      have htarget :
          (⟨s.val + j.val, hsource⟩ : Fin (directionsDeterminedBy points).card) =
          ⟨(s.val + j.val) % (directionsDeterminedBy points).card,
            Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩ := by
        apply Fin.ext
        exact (Nat.mod_eq_of_lt hsource).symm
      simpa [htarget] using h
  · have hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val := by omega
    have h := sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap hcard hne hr hncoll s j hwrap
    have htarget :
        (⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ :
          Fin (directionsDeterminedBy points).card) =
        ⟨(s.val + j.val) % (directionsDeterminedBy points).card,
          Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩ := by
      apply Fin.ext
      have hlt_sub : s.val + j.val - (directionsDeterminedBy points).card <
          (directionsDeterminedBy points).card := by
        omega
      have hmod : (s.val + j.val) % (directionsDeterminedBy points).card =
          s.val + j.val - (directionsDeterminedBy points).card := by
        rw [Nat.mod_eq_sub_mod hwrap]
        exact Nat.mod_eq_of_lt hlt_sub
      exact hmod.symm
    simpa [htarget] using h

theorem sweepConcreteGAS_atIndex_mod_pi_moveOrder_no_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : s.val + j.val + 1 < (directionsDeterminedBy points).card) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).moveOrder j =
      (sweepConcreteGAS hcard hne hr hncoll).moveOrder ⟨s.val + j.val, by omega⟩ := by
  let B := sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s
  let A := sweepConcreteGAS hcard hne hr hncoll
  have hcount : GeneralizedAllowableSequence.crossingLabelsCard B.seq j =
      GeneralizedAllowableSequence.crossingLabelsCard A.seq ⟨s.val + j.val, by omega⟩ := by
    simpa [A, B] using
      sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap hcard hne hr hncoll s j hwrap
  change B.toCountedGeneralizedAllowableSequence.moveOrder j =
    A.toCountedGeneralizedAllowableSequence.moveOrder ⟨s.val + j.val, by omega⟩
  exact CountedGeneralizedAllowableSequence.moveOrder_eq_of_crossingLabelsCard_eq
    B.toCountedGeneralizedAllowableSequence A.toCountedGeneralizedAllowableSequence hcount

theorem sweepConcreteGAS_atIndex_mod_pi_moveOrder_no_wrap_to_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hsource : s.val + j.val < (directionsDeterminedBy points).card)
    (hboundary : s.val + j.val + 1 = (directionsDeterminedBy points).card)
    (hnext : j.val + 1 < (directionsDeterminedBy points).card) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).moveOrder j =
      (sweepConcreteGAS hcard hne hr hncoll).moveOrder
        ⟨s.val + j.val, hsource⟩ := by
  let B := sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s
  let A := sweepConcreteGAS hcard hne hr hncoll
  have hcount : GeneralizedAllowableSequence.crossingLabelsCard B.seq j =
      GeneralizedAllowableSequence.crossingLabelsCard A.seq
        ⟨s.val + j.val, hsource⟩ := by
    simpa [A, B] using
      sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap_to_wrap
        hcard hne hr hncoll s j hsource hboundary hnext
  change B.toCountedGeneralizedAllowableSequence.moveOrder j =
    A.toCountedGeneralizedAllowableSequence.moveOrder ⟨s.val + j.val, hsource⟩
  exact CountedGeneralizedAllowableSequence.moveOrder_eq_of_crossingLabelsCard_eq
    B.toCountedGeneralizedAllowableSequence A.toCountedGeneralizedAllowableSequence hcount





theorem sweepConcreteGAS_atIndex_mod_pi_moveOrder_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).moveOrder j =
      (sweepConcreteGAS hcard hne hr hncoll).moveOrder
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ := by
  let B := sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s
  let A := sweepConcreteGAS hcard hne hr hncoll
  have hcount : GeneralizedAllowableSequence.crossingLabelsCard B.seq j =
      GeneralizedAllowableSequence.crossingLabelsCard A.seq
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ := by
    simpa [A, B] using
      sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap
        hcard hne hr hncoll s j hwrap
  change B.toCountedGeneralizedAllowableSequence.moveOrder j =
    A.toCountedGeneralizedAllowableSequence.moveOrder
      ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩
  exact CountedGeneralizedAllowableSequence.moveOrder_eq_of_crossingLabelsCard_eq
    B.toCountedGeneralizedAllowableSequence A.toCountedGeneralizedAllowableSequence hcount

theorem sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_before
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s idx : Fin (directionsDeterminedBy points).card)
    (hidx : idx.val < s.val) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).moveOrder
        ⟨idx.val + (directionsDeterminedBy points).card - s.val, by omega⟩ =
      (sweepConcreteGAS hcard hne hr hncoll).moveOrder idx := by
  let j : Fin (directionsDeterminedBy points).card :=
    ⟨idx.val + (directionsDeterminedBy points).card - s.val, by omega⟩
  have hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val := by
    dsimp [j]
    omega
  have h := sweepConcreteGAS_atIndex_mod_pi_moveOrder_wrap hcard hne hr hncoll s j hwrap
  have htarget :
      (⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ :
        Fin (directionsDeterminedBy points).card) = idx := by
    apply Fin.ext
    dsimp [j]
    omega
  simpa [j, htarget] using h

theorem sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_at_or_after_nonlast
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s idx : Fin (directionsDeterminedBy points).card)
    (hidx : s.val ≤ idx.val)
    (hnext : idx.val + 1 < (directionsDeterminedBy points).card) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).moveOrder
        ⟨idx.val - s.val, by omega⟩ =
      (sweepConcreteGAS hcard hne hr hncoll).moveOrder idx := by
  let j : Fin (directionsDeterminedBy points).card := ⟨idx.val - s.val, by omega⟩
  have hnowrap : s.val + j.val + 1 < (directionsDeterminedBy points).card := by
    dsimp [j]
    omega
  have h := sweepConcreteGAS_atIndex_mod_pi_moveOrder_no_wrap hcard hne hr hncoll s j hnowrap
  have htarget :
      (⟨s.val + j.val, by omega⟩ : Fin (directionsDeterminedBy points).card) = idx := by
    apply Fin.ext
    dsimp [j]
    omega
  simpa [j, htarget] using h

theorem sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_at_or_after_shifted_nonlast
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s idx : Fin (directionsDeterminedBy points).card)
    (hidx : s.val ≤ idx.val)
    (hshift_next : idx.val - s.val + 1 < (directionsDeterminedBy points).card) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).moveOrder
        ⟨idx.val - s.val, by omega⟩ =
      (sweepConcreteGAS hcard hne hr hncoll).moveOrder idx := by
  by_cases hordinary_next : idx.val + 1 < (directionsDeterminedBy points).card
  · exact sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_at_or_after_nonlast
      hcard hne hr hncoll s idx hidx hordinary_next
  · let j : Fin (directionsDeterminedBy points).card := ⟨idx.val - s.val, by omega⟩
    have hsource : s.val + j.val < (directionsDeterminedBy points).card := by
      dsimp [j]
      omega
    have hboundary : s.val + j.val + 1 = (directionsDeterminedBy points).card := by
      dsimp [j]
      have hle : idx.val + 1 ≤ (directionsDeterminedBy points).card := idx.isLt
      omega
    have hnext : j.val + 1 < (directionsDeterminedBy points).card := by
      dsimp [j]
      omega
    have h := sweepConcreteGAS_atIndex_mod_pi_moveOrder_no_wrap_to_wrap
      hcard hne hr hncoll s j hsource hboundary hnext
    have htarget :
        (⟨s.val + j.val, hsource⟩ : Fin (directionsDeterminedBy points).card) = idx := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa [j, htarget] using h



theorem sweepConcreteGAS_atIndex_mod_pi_isCrossing_no_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : s.val + j.val + 1 < (directionsDeterminedBy points).card) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).IsCrossing j ↔
      (sweepConcreteGAS hcard hne hr hncoll).IsCrossing ⟨s.val + j.val, by omega⟩ := by
  let B := sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s
  let A := sweepConcreteGAS hcard hne hr hncoll
  have hcount : GeneralizedAllowableSequence.crossingLabelsCard B.seq j =
      GeneralizedAllowableSequence.crossingLabelsCard A.seq ⟨s.val + j.val, by omega⟩ := by
    simpa [A, B] using
      sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap hcard hne hr hncoll s j hwrap
  change B.toCountedGeneralizedAllowableSequence.IsCrossing j ↔
    A.toCountedGeneralizedAllowableSequence.IsCrossing ⟨s.val + j.val, by omega⟩
  exact CountedGeneralizedAllowableSequence.isCrossing_iff_of_crossingLabelsCard_eq
    B.toCountedGeneralizedAllowableSequence A.toCountedGeneralizedAllowableSequence hcount

theorem sweepConcreteGAS_atIndex_mod_pi_isCrossing_no_wrap_to_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hsource : s.val + j.val < (directionsDeterminedBy points).card)
    (hboundary : s.val + j.val + 1 = (directionsDeterminedBy points).card)
    (hnext : j.val + 1 < (directionsDeterminedBy points).card) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).IsCrossing j ↔
      (sweepConcreteGAS hcard hne hr hncoll).IsCrossing
        ⟨s.val + j.val, hsource⟩ := by
  let B := sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s
  let A := sweepConcreteGAS hcard hne hr hncoll
  have hcount : GeneralizedAllowableSequence.crossingLabelsCard B.seq j =
      GeneralizedAllowableSequence.crossingLabelsCard A.seq
        ⟨s.val + j.val, hsource⟩ := by
    simpa [A, B] using
      sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap_to_wrap
        hcard hne hr hncoll s j hsource hboundary hnext
  change B.toCountedGeneralizedAllowableSequence.IsCrossing j ↔
    A.toCountedGeneralizedAllowableSequence.IsCrossing ⟨s.val + j.val, hsource⟩
  exact CountedGeneralizedAllowableSequence.isCrossing_iff_of_crossingLabelsCard_eq
    B.toCountedGeneralizedAllowableSequence A.toCountedGeneralizedAllowableSequence hcount





theorem sweepConcreteGAS_atIndex_mod_pi_isCrossing_wrap
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).IsCrossing j ↔
      (sweepConcreteGAS hcard hne hr hncoll).IsCrossing
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ := by
  let B := sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s
  let A := sweepConcreteGAS hcard hne hr hncoll
  have hcount : GeneralizedAllowableSequence.crossingLabelsCard B.seq j =
      GeneralizedAllowableSequence.crossingLabelsCard A.seq
        ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ := by
    simpa [A, B] using
      sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap
        hcard hne hr hncoll s j hwrap
  change B.toCountedGeneralizedAllowableSequence.IsCrossing j ↔
    A.toCountedGeneralizedAllowableSequence.IsCrossing
      ⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩
  exact CountedGeneralizedAllowableSequence.isCrossing_iff_of_crossingLabelsCard_eq
    B.toCountedGeneralizedAllowableSequence A.toCountedGeneralizedAllowableSequence hcount

theorem sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_before
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s idx : Fin (directionsDeterminedBy points).card)
    (hidx : idx.val < s.val) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).IsCrossing
        ⟨idx.val + (directionsDeterminedBy points).card - s.val, by omega⟩ ↔
      (sweepConcreteGAS hcard hne hr hncoll).IsCrossing idx := by
  let j : Fin (directionsDeterminedBy points).card :=
    ⟨idx.val + (directionsDeterminedBy points).card - s.val, by omega⟩
  have hwrap : (directionsDeterminedBy points).card ≤ s.val + j.val := by
    dsimp [j]
    omega
  have h := sweepConcreteGAS_atIndex_mod_pi_isCrossing_wrap hcard hne hr hncoll s j hwrap
  have htarget :
      (⟨s.val + j.val - (directionsDeterminedBy points).card, by omega⟩ :
        Fin (directionsDeterminedBy points).card) = idx := by
    apply Fin.ext
    dsimp [j]
    omega
  simpa [j, htarget] using h

theorem sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_at_or_after_nonlast
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s idx : Fin (directionsDeterminedBy points).card)
    (hidx : s.val ≤ idx.val)
    (hnext : idx.val + 1 < (directionsDeterminedBy points).card) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).IsCrossing
        ⟨idx.val - s.val, by omega⟩ ↔
      (sweepConcreteGAS hcard hne hr hncoll).IsCrossing idx := by
  let j : Fin (directionsDeterminedBy points).card := ⟨idx.val - s.val, by omega⟩
  have hnowrap : s.val + j.val + 1 < (directionsDeterminedBy points).card := by
    dsimp [j]
    omega
  have h := sweepConcreteGAS_atIndex_mod_pi_isCrossing_no_wrap hcard hne hr hncoll s j hnowrap
  have htarget :
      (⟨s.val + j.val, by omega⟩ : Fin (directionsDeterminedBy points).card) = idx := by
    apply Fin.ext
    dsimp [j]
    omega
  simpa [j, htarget] using h

theorem sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_at_or_after_shifted_nonlast
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s idx : Fin (directionsDeterminedBy points).card)
    (hidx : s.val ≤ idx.val)
    (hshift_next : idx.val - s.val + 1 < (directionsDeterminedBy points).card) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).IsCrossing
        ⟨idx.val - s.val, by omega⟩ ↔
      (sweepConcreteGAS hcard hne hr hncoll).IsCrossing idx := by
  by_cases hordinary_next : idx.val + 1 < (directionsDeterminedBy points).card
  · exact sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_at_or_after_nonlast
      hcard hne hr hncoll s idx hidx hordinary_next
  · let j : Fin (directionsDeterminedBy points).card := ⟨idx.val - s.val, by omega⟩
    have hsource : s.val + j.val < (directionsDeterminedBy points).card := by
      dsimp [j]
      omega
    have hboundary : s.val + j.val + 1 = (directionsDeterminedBy points).card := by
      dsimp [j]
      have hle : idx.val + 1 ≤ (directionsDeterminedBy points).card := idx.isLt
      omega
    have hnext : j.val + 1 < (directionsDeterminedBy points).card := by
      dsimp [j]
      omega
    have h := sweepConcreteGAS_atIndex_mod_pi_isCrossing_no_wrap_to_wrap
      hcard hne hr hncoll s j hsource hboundary hnext
    have htarget :
        (⟨s.val + j.val, hsource⟩ : Fin (directionsDeterminedBy points).card) = idx := by
      apply Fin.ext
      dsimp [j]
      omega
    simpa [j, htarget] using h

theorem sweepConcreteGAS_atIndex_mod_pi_isCrossing_shifted_nonfinal
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (s j : Fin (directionsDeterminedBy points).card)
    (hnext : j.val + 1 < (directionsDeterminedBy points).card) :
    (sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s).IsCrossing j ↔
      (sweepConcreteGAS hcard hne hr hncoll).IsCrossing
        ⟨(s.val + j.val) % (directionsDeterminedBy points).card,
          Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩ := by
  let B := sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s
  let A := sweepConcreteGAS hcard hne hr hncoll
  have hcount : GeneralizedAllowableSequence.crossingLabelsCard B.seq j =
      GeneralizedAllowableSequence.crossingLabelsCard A.seq
        ⟨(s.val + j.val) % (directionsDeterminedBy points).card,
          Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩ := by
    simpa [A, B] using
      sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_shifted_nonfinal
        hcard hne hr hncoll s j hnext
  change B.toCountedGeneralizedAllowableSequence.IsCrossing j ↔
    A.toCountedGeneralizedAllowableSequence.IsCrossing
      ⟨(s.val + j.val) % (directionsDeterminedBy points).card,
        Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩
  exact CountedGeneralizedAllowableSequence.isCrossing_iff_of_crossingLabelsCard_eq
    B.toCountedGeneralizedAllowableSequence A.toCountedGeneralizedAllowableSequence hcount

noncomputable def sweepConcreteGAS_cyclicEndGapWitness_of_noFull
    {points : Finset Point2} {k : ℕ}
    (hcard : points.card = 2 * k)
    (hk : 0 < k)
    (hne : (directionsDeterminedBy points).Nonempty)
    (hr : 2 ≤ (directionsDeterminedBy points).card)
    (hncoll : NoncollinearSet points)
    (hnoFull :
      ∀ j : Fin (directionsDeterminedBy points).card,
        (sweepConcreteGAS hcard hne hr hncoll).IsCrossing j →
          (sweepConcreteGAS hcard hne hr hncoll).moveOrder j < k) :
    (sweepConcreteGAS hcard hne hr hncoll).CyclicEndGapWitness
      ((sweepConcreteGAS hcard hne hr hncoll).toCountedGeneralizedAllowableSequence
        |>.crossingMoves_card_pos hk) := by
  let A := sweepConcreteGAS hcard hne hr hncoll
  let AC := A.toCountedGeneralizedAllowableSequence
  have hpos : 0 < AC.crossingMoves.card := AC.crossingMoves_card_pos hk
  have htwo : 2 ≤ AC.crossingMoves.card := by
    exact AC.two_le_crossingMoves_card_of_no_full_crossing hk (by
      intro j hj
      exact hnoFull j (by simpa [A, AC] using hj))
  let firstOrd : Fin (directionsDeterminedBy points).card :=
    AC.crossingIdx ⟨0, hpos⟩
  let lastOrd : Fin (directionsDeterminedBy points).card :=
    AC.crossingIdx ⟨AC.crossingMoves.card - 1, by omega⟩
  have hfirst_lt_last : firstOrd.val < lastOrd.val := by
    have hfinlt :
        (⟨0, hpos⟩ : Fin AC.crossingMoves.card) <
          ⟨AC.crossingMoves.card - 1, by omega⟩ := by
      change 0 < AC.crossingMoves.card - 1
      omega
    exact AC.crossingIdx_strict hfinlt
  have hlast_pos : 0 < lastOrd.val := by omega
  let s : Fin (directionsDeterminedBy points).card := lastOrd
  let B := sweepConcreteGAS_atIndex_mod_pi hcard hne hr hncoll s
  let lastB : Fin (directionsDeterminedBy points).card :=
    ⟨lastOrd.val - s.val, by omega⟩
  let nextFirstB : Fin (directionsDeterminedBy points).card :=
    ⟨firstOrd.val + (directionsDeterminedBy points).card - lastOrd.val, by omega⟩
  have hlastB_zero : lastB.val = 0 := by
    dsimp [lastB, s]
    omega
  have hnextFirstB_pos : 0 < nextFirstB.val := by
    dsimp [nextFirstB]
    omega
  have hnextFirstB_lt : nextFirstB.val < (directionsDeterminedBy points).card :=
    nextFirstB.isLt
  have hlastB_cross : B.IsCrossing lastB := by
    have h :=
      (sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_at_or_after_shifted_nonlast
        hcard hne hr hncoll s lastOrd (by simp [s]) (by
          dsimp [s]
          have hrpos : 0 < (directionsDeterminedBy points).card :=
            Finset.card_pos.mpr hne
          omega)).mpr
        (by simpa [A, AC, lastOrd] using
          AC.crossingIdx_isCrossing ⟨AC.crossingMoves.card - 1, by omega⟩)
    simpa [B, A, lastB, s] using h
  have hnextFirstB_cross : B.IsCrossing nextFirstB := by
    have h :=
      (sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_before
        hcard hne hr hncoll s firstOrd (by simpa [s] using hfirst_lt_last)).mpr
        (by simpa [A, AC, firstOrd] using AC.crossingIdx_isCrossing ⟨0, hpos⟩)
    simpa [B, A, nextFirstB, s] using h
  refine
    { periodMoves := (directionsDeterminedBy points).card
      cyclic := B
      lastCrossing := lastB
      nextFirstCrossing := nextFirstB
      consecutive := ?_
      last_order := ?_
      next_order := ?_
      cyclic_gap_eq := ?_ }
  · refine ⟨hlastB_cross, hnextFirstB_cross, ?_, ?_⟩
    · omega
    · intro l hlast_l hl_first hBl
      have hlnext : l.val + 1 < (directionsDeterminedBy points).card := by
        omega
      let idx : Fin (directionsDeterminedBy points).card :=
        ⟨(s.val + l.val) % (directionsDeterminedBy points).card,
          Nat.mod_lt _ (Finset.card_pos.mpr hne)⟩
      have hAidx : AC.IsCrossing idx := by
        have hrot :=
          (sweepConcreteGAS_atIndex_mod_pi_isCrossing_shifted_nonfinal
            hcard hne hr hncoll s l hlnext).mp (by simpa [B] using hBl)
        simpa [A, AC, idx] using hrot
      by_cases hnowrap : s.val + l.val < (directionsDeterminedBy points).card
      · have hidx_after : lastOrd.val < idx.val := by
          dsimp [idx, s]
          rw [Nat.mod_eq_of_lt hnowrap]
          omega
        exact (AC.not_isCrossing_after_last_crossingIdx hpos (j := idx) hidx_after) hAidx
      · have hwrap : (directionsDeterminedBy points).card ≤ s.val + l.val := by omega
        have hidx_before : idx.val < firstOrd.val := by
          dsimp [idx, s, nextFirstB] at hl_first ⊢
          have hlt_sub : lastOrd.val + l.val - (directionsDeterminedBy points).card <
              (directionsDeterminedBy points).card := by
            omega
          have hmod : (lastOrd.val + l.val) % (directionsDeterminedBy points).card =
              lastOrd.val + l.val - (directionsDeterminedBy points).card := by
            rw [Nat.mod_eq_sub_mod hwrap]
            exact Nat.mod_eq_of_lt hlt_sub
          rw [hmod]
          omega
        exact (AC.not_isCrossing_before_first_crossingIdx hpos (j := idx) hidx_before) hAidx
  · have h :=
      sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_at_or_after_shifted_nonlast
        hcard hne hr hncoll s lastOrd (by simp [s]) (by
          dsimp [s]
          have hrpos : 0 < (directionsDeterminedBy points).card :=
            Finset.card_pos.mpr hne
          omega)
    simpa [A, B, AC, lastB, lastOrd, s] using h
  · have h :=
      sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_before
        hcard hne hr hncoll s firstOrd (by simpa [s] using hfirst_lt_last)
    simpa [A, B, AC, nextFirstB, firstOrd, s] using h
  · have hgap :
        nextFirstB.val - lastB.val - 1 =
          firstOrd.val + ((directionsDeterminedBy points).card - 1 - lastOrd.val) := by
      have hlast_lt : lastOrd.val < (directionsDeterminedBy points).card := lastOrd.isLt
      dsimp [nextFirstB, lastB]
      omega
    simpa [A, AC, firstOrd, lastOrd] using hgap











-- Starting angle θ₀ is between sortedAngleAt(s-1) and sortedAngleAt(s)
-- (or equivalently, in the gap before event s).
--
-- This records why the older non-cyclic start hypothesis `θ₀ < d.angle` for
-- every direction cannot support a shifted cyclic start: combined with the
-- gap-before-s hypothesis, it forces `s = 0`.


/-!
### Shifted cyclic sweep

The proof of `cyclic_end_gap` starts a second sweep in the gap between the last
and first crossing directions, turning the cyclic end gap into an interior
consecutive-crossing gap.  The local modulo-`π` start infrastructure is wired
into a concrete shifted sweep:

- `orientedLevel_injective_of_all_angles_mod_pi`
- `sweepLabelingAt_inj_mod_pi`
- `sweepGAS_at_mod_pi`
- the `_mod_pi` start/end bounds for `shiftedSortedAngleAt` and
  `interEventAngleAt`
- the no-wrap/wrap angle-identification lemmas, culminating in the
  rotation formulas `shiftedSortedAngleAt_rotate` and
  `interEventAngleAt_rotate`
- `interEventAngleAt_no_other_shiftedEventAngle`
- `only_event_between_interEventAnglesAt_mod_pi`
- `inj_at_interEventAngleAt_mod_pi`
- `mono_at_eventAt_mod_pi`
- `sweepConcreteGAS_at_mod_pi`
- `sweepConcreteGAS_atIndex_mod_pi`
- `sweepLabelingAt_interEventAngle_point_eq`
- `sweepSort_labelingAt_interEventAngle_no_wrap`
- `sweepSort_labelingAt_interEventAngle_wrap`
- `sweepSort_labelingAt_interEventAngle_wrap_rev`
- `sweepConcreteGAS_atIndex_mod_pi_seq_no_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_seq_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_seq_wrap_rev`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_no_wrap_to_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap_last`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_index_before`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_index_at_or_after_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_index_at_or_after_shifted_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_crossingLabelsCard_shifted_nonfinal`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_no_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_no_wrap_to_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_wrap_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_wrap_last`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_before`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_at_or_after_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_index_at_or_after_shifted_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_moveOrder_shifted_nonfinal`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_no_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_no_wrap_to_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_wrap_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_wrap_last`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_wrap`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_before`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_at_or_after_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_index_at_or_after_shifted_nonlast`
- `sweepConcreteGAS_atIndex_mod_pi_isCrossing_shifted_nonfinal`

The transfer is split into the interior no-wrap case, the boundary where the
target state first wraps past `π`, and the nonfinal/final wrapped cases.  These
cases feed `sweepConcreteGAS_cyclicEndGapWitness_of_noFull`, where the ordinary
last crossing becomes the shifted crossing at index `0`, the ordinary first
crossing becomes the next shifted crossing, and the `crossingIdx` extremality
lemmas rule out shifted crossings between them.
-/

end ProofsInTheBook.Chapter11


