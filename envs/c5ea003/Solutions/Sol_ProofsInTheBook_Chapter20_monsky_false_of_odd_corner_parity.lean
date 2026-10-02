-- Prove2me | solution 1 for ProofsInTheBook.Chapter20.monsky_false_of_odd_corner_parity
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T17:51:08.377885+00:00
-- url     : https://prove2.me/submissions/24ef46f6-0cc4-4ec9-b5b3-444489ac42c8

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20


/- Original source header (imports hoisted):
import Mathlib
-/
/- Source module: ProofsInTheBook.Chapter20 -/
section
set_option autoImplicit true


/-!
# Chapter 20: One square and an odd number of triangles

From "Proofs from THE BOOK":

**Monsky's theorem**: A square cannot be divided into an odd number
of triangles of equal area.

The book's proof uses a 2-adic valuation argument: define a coloring
of the plane using the 2-adic valuation of coordinates, then apply
Sperner's lemma to show the triangulation must have an even count.

Formalization status: this file closes the finite coloring and parity layer.
It defines Monsky's three colors, red-green boundary edges, trichromatic
triangles, proves the local parity identity, proves an abstract Sperner
parity theorem, and derives `chapter20`: a `MonskyCertificate n` yields a
trichromatic triangle.  It also packages Mathlib's local-subring/Zorn
infrastructure into `exists_valuation_extension`, which gives an extension of
any valuation on a field to any field extension; in particular
`exists_real_twoAdic_extension` extends `Rat.padicValuation 2` from `ℚ` to `ℝ`.
Using one chosen extension, the file defines Monsky's coloring on `ℝ²`, proves
the unit-square side color constraints, proves the odd red-green boundary
count for any finite subdivision of the square boundary, identifies that count
with an explicit finite list of unit-square boundary point-edges, constructs
`MonskyCertificate` from finite unordered-edge parity, and proves the valuation
contradiction for a trichromatic triangle of ordinary real area `1 / n` with
`n` odd.

Gap to the full book theorem: the remaining work is geometric triangulation
infrastructure.  One needs a finite real triangulation model for the unit
square and an extraction theorem producing:
1. a finite vertex type `α`, a point map `vertices : α → ℝ × ℝ`, and triangles
   `triangles : Fin n → α × α × α`;
2. four side subdivision lists `bottom right top left : List ℝ`, or equivalently
   the explicit point-edge chain `realTwoAdicSquareBoundaryPointEdgeList`;
3. the boundary-incidence theorem that the odd-multiplicity triangle edges are
   exactly that square boundary chain after mapping boundary points to the
   finite vertex type;
4. the ordinary equal-area fact
   `∀ i, realTriangleArea ... = (1 / n : ℚ)`.
Mathlib has `Analysis.Convex.SimplicialComplex` and `Geometry.Polygon.Basic`,
but not this assembled theorem extracting boundary chains and equal-area facts
from a triangulation of the unit square.
-/

namespace ProofsInTheBook.Chapter20

open IsLocalRing









open MonskyColor





















theorem colorOfValues_eq_red_iff {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {vx vy : Γ} :
    colorOfValues vx vy = red ↔ vx < 1 ∧ vy < 1 := by
  unfold colorOfValues
  by_cases hred : vx < 1 ∧ vy < 1
  · simp [hred]
  · by_cases hgreen : 1 ≤ vx ∧ vy ≤ vx
    · simp [hred, hgreen]
    · simp [hred, hgreen]

theorem colorOfValues_green_le {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {vx vy : Γ} (h : colorOfValues vx vy = green) : 1 ≤ vx ∧ vy ≤ vx := by
  unfold colorOfValues at h
  by_cases hred : vx < 1 ∧ vy < 1
  · simp [hred] at h
  · by_cases hgreen : 1 ≤ vx ∧ vy ≤ vx
    · exact hgreen
    · simp [hred, hgreen] at h



theorem colorOfValues_blue_lt_and_one_le {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    {vx vy : Γ} (h : colorOfValues vx vy = blue) : vx < vy ∧ 1 ≤ vy := by
  unfold colorOfValues at h
  by_cases hred : vx < 1 ∧ vy < 1
  · simp [hred] at h
  · by_cases hgreen : 1 ≤ vx ∧ vy ≤ vx
    · simp [hred, hgreen] at h
    · simp [hred, hgreen] at h
      have hvx_lt_one_or : vx < 1 ∨ 1 ≤ vx := lt_or_ge vx 1
      have hvy_lt_or : vy < 1 ∨ 1 ≤ vy := lt_or_ge vy 1
      constructor
      · by_contra hnot
        have hvyle : vy ≤ vx := le_of_not_gt hnot
        rcases hvx_lt_one_or with hvxlt | hvxge
        · have hvylt : vy < 1 := lt_of_le_of_lt hvyle hvxlt
          exact hred ⟨hvxlt, hvylt⟩
        · exact hgreen ⟨hvxge, hvyle⟩
      · rcases hvy_lt_or with hvylt | hvyge
        · rcases hvx_lt_one_or with hvxlt | hvxge
          · exact (hred ⟨hvxlt, hvylt⟩).elim
          · exact (hgreen ⟨hvxge, (le_of_lt hvylt).trans hvxge⟩).elim
        · exact hvyge















theorem abs_doubleArea_eq_two_div_of_realTriangleArea_eq_one_div
    {n : ℕ} (hn : n ≠ 0) {a b c : ℝ × ℝ}
    (harea : realTriangleArea a b c = (((1 : ℚ) / n : ℚ) : ℝ)) :
    |doubleArea a b c| = (((2 : ℚ) / n : ℚ) : ℝ) := by
  have hareaR : realTriangleArea a b c = (1 : ℝ) / n := by
    simpa using harea
  have h := congrArg (fun x : ℝ => x * 2) hareaR
  unfold realTriangleArea at h
  have hR : |doubleArea a b c| = (2 : ℝ) / n := by
    field_simp [Nat.cast_ne_zero.mpr hn] at h ⊢
    linarith
  simpa using hR

/--
A red-green-blue triangle has double area with valuation at least `1` in
Mathlib's multiplicative convention.  This is the valuation side of Monsky's
area contradiction; an odd equal subdivision will later give double area
`2 / n`, whose 2-adic valuation is `< 1`.
-/
theorem valuation_doubleArea_red_green_blue
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) {r g b : K × K}
    (hr : valuationColor v r = red)
    (hg : valuationColor v g = green)
    (hb : valuationColor v b = blue) :
    1 ≤ v (doubleArea r g b) := by
  have hr_lt : v r.1 < 1 ∧ v r.2 < 1 := colorOfValues_eq_red_iff.mp hr
  have hg_le : 1 ≤ v g.1 ∧ v g.2 ≤ v g.1 := colorOfValues_green_le hg
  have hb_lt : v b.1 < v b.2 ∧ 1 ≤ v b.2 := colorOfValues_blue_lt_and_one_le hb
  have hrgx : v (g.1 - r.1) = v g.1 := by
    exact v.map_sub_eq_of_lt_left (lt_of_lt_of_le hr_lt.1 hg_le.1)
  have hrby : v (b.2 - r.2) = v b.2 := by
    exact v.map_sub_eq_of_lt_left (lt_of_lt_of_le hr_lt.2 hb_lt.2)
  have hrgy_le : v (g.2 - r.2) ≤ v g.1 := by
    exact v.map_sub_le hg_le.2 ((le_of_lt hr_lt.2).trans hg_le.1)
  have hrbx_lt : v (b.1 - r.1) < v b.2 := by
    exact lt_of_le_of_lt (v.map_sub b.1 r.1)
      (max_lt hb_lt.1 (lt_of_lt_of_le hr_lt.1 hb_lt.2))
  let t₁ : K := (g.1 - r.1) * (b.2 - r.2)
  let t₂ : K := (b.1 - r.1) * (g.2 - r.2)
  have ht₁ : v t₁ = v g.1 * v b.2 := by
    simp [t₁, hrgx, hrby]
  have ht₂_lt : v t₂ < v g.1 * v b.2 := by
    have hle :
        v (b.1 - r.1) * v (g.2 - r.2) ≤ v (b.1 - r.1) * v g.1 :=
      mul_le_mul' le_rfl hrgy_le
    have hlt : v (b.1 - r.1) * v g.1 < v b.2 * v g.1 := by
      exact (strictMono_mul_right_of_pos (lt_of_lt_of_le zero_lt_one hg_le.1)) hrbx_lt
    have hmul : v (b.1 - r.1) * v (g.2 - r.2) < v b.2 * v g.1 :=
      lt_of_le_of_lt hle hlt
    simpa [t₂, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hdet : v (doubleArea r g b) = v g.1 * v b.2 := by
    change v (t₁ - t₂) = v g.1 * v b.2
    rw [v.map_sub_eq_of_lt_left]
    · exact ht₁
    · rw [ht₁]
      exact ht₂_lt
  rw [hdet]
  calc
    (1 : Γ) = 1 * 1 := by rw [mul_one]
    _ ≤ v g.1 * v b.2 := mul_le_mul' hg_le.1 hb_lt.2





theorem realTwoAdic_hasExtension :
    (Rat.padicValuation 2).HasExtension realTwoAdicValuation :=
  Classical.choose_spec exists_real_twoAdic_extension

/-- Odd natural numbers have 2-adic valuation `1` in multiplicative notation. -/
theorem rat_twoAdicValuation_natCast_of_odd {n : ℕ} (hn : Odd n) :
    Rat.padicValuation 2 (n : ℚ) = 1 := by
  have hnotdvd_nat : ¬ 2 ∣ n := by
    intro h
    exact (Nat.not_even_iff_odd.mpr hn) ((even_iff_two_dvd).2 h)
  have hnotdvd_int : ¬ (2 : ℤ) ∣ (n : ℤ) := by
    exact_mod_cast hnotdvd_nat
  change Rat.padicValuation 2 (((n : ℤ) : ℚ)) = 1
  rw [Rat.padicValuation_cast]
  exact (Int.padicValuation_eq_one_iff (p := 2) (x := (n : ℤ))).2 hnotdvd_int

/-- If `n` is odd, the rational double area `2 / n` has 2-adic valuation `< 1`. -/
theorem rat_twoAdicValuation_two_div_odd_lt_one {n : ℕ} (hn : Odd n) :
    Rat.padicValuation 2 ((2 : ℚ) / n) < 1 := by
  rw [map_div₀]
  have h2 : Rat.padicValuation 2 ((2 : ℚ)) = WithZero.exp (-1 : ℤ) := by
    simpa using Rat.padicValuation_self 2
  rw [h2, rat_twoAdicValuation_natCast_of_odd hn, div_one]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

/--
The same `< 1` estimate after transporting `2 / n` into the chosen real
2-adic valuation extension.
-/
theorem realTwoAdicValuation_rat_two_div_odd_lt_one {n : ℕ} (hn : Odd n) :
    realTwoAdicValuation (((2 : ℚ) / n : ℚ) : ℝ) < 1 := by
  letI : (Rat.padicValuation 2).HasExtension realTwoAdicValuation := realTwoAdic_hasExtension
  have hrat :
      Rat.padicValuation 2 (((2 : ℚ) / n : ℚ)) < Rat.padicValuation 2 (1 : ℚ) := by
    simpa using rat_twoAdicValuation_two_div_odd_lt_one hn
  have h := (Valuation.HasExtension.val_map_lt_iff
    (vR := Rat.padicValuation 2) (vA := realTwoAdicValuation) (((2 : ℚ) / n : ℚ)) 1).2 hrat
  simpa using h



/--
A red-green-blue triangle cannot have rational double area `2 / n` when `n`
is odd.  This is the valuation contradiction at the end of Monsky's proof,
separated from the still-missing geometric construction of the finite
triangulation certificate.
-/
theorem not_real_doubleArea_eq_two_div_odd_of_red_green_blue {n : ℕ} (hn : Odd n)
    {r g b : ℝ × ℝ}
    (hr : realTwoAdicColor r = red)
    (hg : realTwoAdicColor g = green)
    (hb : realTwoAdicColor b = blue)
    (harea : doubleArea r g b = (((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  have hge : 1 ≤ realTwoAdicValuation (doubleArea r g b) := by
    exact valuation_doubleArea_red_green_blue realTwoAdicValuation
      (by simpa [realTwoAdicColor] using hr)
      (by simpa [realTwoAdicColor] using hg)
      (by simpa [realTwoAdicColor] using hb)
  rw [harea] at hge
  exact not_lt_of_ge hge (realTwoAdicValuation_rat_two_div_odd_lt_one hn)

/-- Negating the odd-denominator rational double area does not change the 2-adic bound. -/
theorem realTwoAdicValuation_neg_rat_two_div_odd_lt_one {n : ℕ} (hn : Odd n) :
    realTwoAdicValuation (-(((2 : ℚ) / n : ℚ) : ℝ)) < 1 := by
  simpa using realTwoAdicValuation_rat_two_div_odd_lt_one hn

/-- The negative-orientation variant of the Monsky area contradiction. -/
theorem not_real_doubleArea_eq_neg_two_div_odd_of_red_green_blue {n : ℕ} (hn : Odd n)
    {r g b : ℝ × ℝ}
    (hr : realTwoAdicColor r = red)
    (hg : realTwoAdicColor g = green)
    (hb : realTwoAdicColor b = blue)
    (harea : doubleArea r g b = -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  have hge : 1 ≤ realTwoAdicValuation (doubleArea r g b) := by
    exact valuation_doubleArea_red_green_blue realTwoAdicValuation
      (by simpa [realTwoAdicColor] using hr)
      (by simpa [realTwoAdicColor] using hg)
      (by simpa [realTwoAdicColor] using hb)
  rw [harea] at hge
  exact not_lt_of_ge hge (realTwoAdicValuation_neg_rat_two_div_odd_lt_one hn)

































/-- `TrichromaticTriangle` is invariant under swapping the last two vertices. -/
theorem trichromaticTriangle_swap_right {a b c : MonskyColor} :
    TrichromaticTriangle a b c ↔ TrichromaticTriangle a c b := by
  cases a <;> cases b <;> cases c <;> decide

/--
Any trichromatic triangle with odd rational double area contradicts the chosen
real 2-adic Monsky coloring.  The case split only reorders the three vertices
so that the area estimate sees them in red-green-blue order.
-/
theorem not_real_doubleArea_eq_two_div_odd_of_trichromatic {n : ℕ} (hn : Odd n)
    {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c))
    (harea : doubleArea a b c = (((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  generalize hca : realTwoAdicColor a = ca at htri
  generalize hcb : realTwoAdicColor b = cb at htri
  generalize hcc : realTwoAdicColor c = cc at htri
  cases ca <;> cases cb <;> cases cc <;> simp [TrichromaticTriangle] at htri
  · exact not_real_doubleArea_eq_two_div_odd_of_red_green_blue hn hca hcb hcc harea
  · have hperm : doubleArea a c b = -doubleArea a b c := by
      unfold doubleArea
      ring
    have harea' : doubleArea a c b = -(((2 : ℚ) / n : ℚ) : ℝ) := by
      rw [hperm, harea]
    exact not_real_doubleArea_eq_neg_two_div_odd_of_red_green_blue hn hca hcc hcb harea'
  · have hperm : doubleArea b a c = -doubleArea a b c := by
      unfold doubleArea
      ring
    have harea' : doubleArea b a c = -(((2 : ℚ) / n : ℚ) : ℝ) := by
      rw [hperm, harea]
    exact not_real_doubleArea_eq_neg_two_div_odd_of_red_green_blue hn hcb hca hcc harea'
  · have hperm : doubleArea c a b = doubleArea a b c := by
      unfold doubleArea
      ring
    have harea' : doubleArea c a b = (((2 : ℚ) / n : ℚ) : ℝ) := by
      rw [hperm, harea]
    exact not_real_doubleArea_eq_two_div_odd_of_red_green_blue hn hcc hca hcb harea'
  · have hperm : doubleArea b c a = doubleArea a b c := by
      unfold doubleArea
      ring
    have harea' : doubleArea b c a = (((2 : ℚ) / n : ℚ) : ℝ) := by
      rw [hperm, harea]
    exact not_real_doubleArea_eq_two_div_odd_of_red_green_blue hn hcb hcc hca harea'
  · have hperm : doubleArea c b a = -doubleArea a b c := by
      unfold doubleArea
      ring
    have harea' : doubleArea c b a = -(((2 : ℚ) / n : ℚ) : ℝ) := by
      rw [hperm, harea]
    exact not_real_doubleArea_eq_neg_two_div_odd_of_red_green_blue hn hcc hcb hca harea'

/-- The negative-orientation form of `not_real_doubleArea_eq_two_div_odd_of_trichromatic`. -/
theorem not_real_doubleArea_eq_neg_two_div_odd_of_trichromatic {n : ℕ} (hn : Odd n)
    {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c))
    (harea : doubleArea a b c = -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  have hperm : doubleArea a c b = -doubleArea a b c := by
    unfold doubleArea
    ring
  have harea' : doubleArea a c b = (((2 : ℚ) / n : ℚ) : ℝ) := by
    rw [hperm, harea]
    simp
  exact not_real_doubleArea_eq_two_div_odd_of_trichromatic hn
    (trichromaticTriangle_swap_right.mp htri) harea'

/-- Orientation-free odd equal-area contradiction for a trichromatic triangle. -/
theorem not_real_doubleArea_eq_abs_two_div_odd_of_trichromatic {n : ℕ} (hn : Odd n)
    {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c))
    (harea : doubleArea a b c = (((2 : ℚ) / n : ℚ) : ℝ) ∨
      doubleArea a b c = -(((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  rcases harea with harea | harea
  · exact not_real_doubleArea_eq_two_div_odd_of_trichromatic hn htri harea
  · exact not_real_doubleArea_eq_neg_two_div_odd_of_trichromatic hn htri harea

theorem real_two_div_natCast_nonneg_of_odd {n : ℕ} (hn : Odd n) :
    (0 : ℝ) ≤ (((2 : ℚ) / n : ℚ) : ℝ) := by
  rcases hn with ⟨k, hk⟩
  have hnpos : 0 < n := by omega
  positivity

/--
Absolute double area is the usual orientation-free area input.  For odd `n`,
the valuation contradiction only needs the two oriented alternatives obtained
from `|doubleArea| = 2 / n`.
-/
theorem not_real_abs_doubleArea_eq_two_div_odd_of_trichromatic {n : ℕ} (hn : Odd n)
    {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c))
    (harea : |doubleArea a b c| = (((2 : ℚ) / n : ℚ) : ℝ)) : False := by
  exact not_real_doubleArea_eq_abs_two_div_odd_of_trichromatic hn htri
    ((abs_eq (real_two_div_natCast_nonneg_of_odd hn)).mp harea)

/--
Area form of the trichromatic valuation contradiction: a trichromatic triangle
cannot have ordinary real area `1 / n` when `n` is odd.
-/
theorem not_real_triangleArea_eq_one_div_odd_of_trichromatic {n : ℕ} (hn : Odd n)
    {a b c : ℝ × ℝ}
    (htri : TrichromaticTriangle (realTwoAdicColor a) (realTwoAdicColor b)
      (realTwoAdicColor c))
    (harea : realTriangleArea a b c = (((1 : ℚ) / n : ℚ) : ℝ)) : False := by
  have hn0 : n ≠ 0 := by
    rcases hn with ⟨k, hk⟩
    omega
  exact not_real_abs_doubleArea_eq_two_div_odd_of_trichromatic hn htri
    (abs_doubleArea_eq_two_div_of_realTriangleArea_eq_one_div hn0 harea)



























































/--
Local Sperner parity atom: a triangle is trichromatic exactly when it has an
odd number of red-green edges.
-/
theorem odd_redGreenEdges_iff_trichromatic (a b c : MonskyColor) :
    Odd
      ((if RedGreenEdge a b then 1 else 0 : ℕ) +
       (if RedGreenEdge b c then 1 else 0 : ℕ) +
       (if RedGreenEdge c a then 1 else 0 : ℕ)) ↔
      TrichromaticTriangle a b c := by
  cases a <;> cases b <;> cases c <;> decide





























































/--
Abstract Sperner parity lemma: in a finite triangulation where each edge
belongs to at most two triangles, the number of trichromatic triangles has
the same parity as the number of red-green boundary edges.

`triangles` is the finite set of triangles, each given by three color assignments.
`boundaryRG` counts red-green edges on the boundary (shared by exactly one triangle).
-/
private theorem sum_nat_mod_two_eq_sum_mod_two
    {α : Type*} (s : Finset α) (f : α → ℕ) :
    (∑ x ∈ s, f x) % 2 = (∑ x ∈ s, f x % 2) % 2 := by
  classical
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    conv_lhs => rw [Nat.add_mod (f a) _ 2, ih]
    conv_rhs => rw [Nat.add_mod (f a % 2) _ 2]
    simp







theorem sperner_parity_abstract
    (n : ℕ) (triangleColors : Fin n → MonskyColor × MonskyColor × MonskyColor)
    (boundaryRGCount : ℕ)
    (totalRG : ℕ)
    (htotal : totalRG = ∑ i : Fin n,
      ((if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0)))
    (hparity : totalRG % 2 = boundaryRGCount % 2) :
    (Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2).card % 2 = boundaryRGCount % 2 := by
  classical
  let f : Fin n → ℕ := fun i =>
    (if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
    (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
    (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0)
  let T : Fin n → Prop := fun i =>
    TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
      (triangleColors i).2.2
  have hlocal : ∀ i : Fin n, f i % 2 = if T i then 1 else 0 := by
    intro i
    have hodd := odd_redGreenEdges_iff_trichromatic (triangleColors i).1
      (triangleColors i).2.1 (triangleColors i).2.2
    by_cases ht : T i
    · rw [if_pos ht]
      exact Nat.odd_iff.mp (hodd.mpr ht)
    · rw [if_neg ht]
      by_contra h
      have : f i % 2 = 1 := by omega
      exact ht (hodd.mp (Nat.odd_iff.mpr this))
  have hreplace : (∑ i : Fin n, f i % 2) = ∑ i : Fin n, if T i then 1 else 0 :=
    Finset.sum_congr rfl fun i _ => hlocal i
  have hcard : (∑ i : Fin n, if T i then (1 : ℕ) else 0) =
      (Finset.univ.filter T).card := by
    rw [← Finset.sum_filter]; simp
  calc (Finset.univ.filter T).card % 2
      = (∑ i : Fin n, if T i then (1 : ℕ) else 0) % 2 := by rw [hcard]
    _ = (∑ i : Fin n, f i % 2) % 2 := by rw [hreplace]
    _ = (∑ i : Fin n, f i) % 2 := (sum_nat_mod_two_eq_sum_mod_two _ _).symm
    _ = totalRG % 2 := by rw [htotal]
    _ = boundaryRGCount % 2 := hparity

/--
Corollary: if the boundary red-green edge count is odd, at least one triangle
is trichromatic.
-/
theorem exists_trichromatic_of_odd_boundary
    (n : ℕ) (triangleColors : Fin n → MonskyColor × MonskyColor × MonskyColor)
    (boundaryRGCount : ℕ)
    (totalRG : ℕ)
    (htotal : totalRG = ∑ i : Fin n,
      ((if RedGreenEdge (triangleColors i).1 (triangleColors i).2.1 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.1 (triangleColors i).2.2 then 1 else 0) +
       (if RedGreenEdge (triangleColors i).2.2 (triangleColors i).1 then 1 else 0)))
    (hparity : totalRG % 2 = boundaryRGCount % 2)
    (hodd : Odd boundaryRGCount) :
    ∃ i : Fin n,
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2 := by
  by_contra hall
  push Not at hall
  have hempty : (Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i _
    exact hall i
  have hcard0 : (Finset.univ.filter fun i : Fin n =>
      TrichromaticTriangle (triangleColors i).1 (triangleColors i).2.1
        (triangleColors i).2.2).card = 0 := by
    simp [hempty]
  have := sperner_parity_abstract n triangleColors boundaryRGCount totalRG htotal hparity
  rw [hcard0] at this
  rcases hodd with ⟨k, hk⟩
  omega





/-
Remaining geometric interface: given a hypothetical equal-area triangulation
of the unit square into an odd number of real triangles, one still needs to
extract the finite list of triangle vertices, identify the odd-multiplicity
triangle edges with the explicit square boundary point-edge chain, and express
the equal-area hypothesis as oriented double area `± 2 / n` for each listed
triangle.
-/



















































/-! ### Linear-algebra bridge for `doubleArea`

The signed double-area `doubleArea a b c` is the determinant of the linear map
on `ℝ²` whose standard-basis images are the edge vectors `b - a` and `c - a`.
This rephrasing is the foundation for connecting the chapter's combinatorial
oriented area to Mathlib's `addHaar_image_linearMap` change-of-variables
formula — the route by which a future geometric dissection of the unit square
will deliver the boundary edge-parity (`hboundary`) needed to remove the
remaining `MonskyCertificate` escape.
-/





/-! ### Structural properties of `doubleArea`

Translation invariance, vertex-permutation symmetries, and the collinearity
equivalence — small structural lemmas needed for any future geometric work
on triangle dissections of the unit square (Monsky's remaining frontier).
-/



















/-! ### Affine parametrization of the triangle by the filled 2-simplex

The triangle with vertices `a, b, c` is the image, under the affine map
`(s, t) ↦ a + s • (b - a) + t • (c - a)`, of the filled standard 2-simplex
`{(s, t) | 0 ≤ s, 0 ≤ t, s + t ≤ 1}`.  We define the parametrization and
prove the forward containment (image ⊆ convex hull).  Pairing this with the
2-dimensional Lebesgue volume formula for linear-map images is the route to
`volume (convexHull ℝ {a, b, c}) = realTriangleArea a b c`.
-/



















/-! ### Brick 1: volume of the filled 2-simplex

The 2-dimensional Lebesgue measure of `filled2Simplex` equals `1/2`.
Direct Fubini route: slice the simplex at fixed `x`, identify the slice
with `Icc 0 (1-x)`, and integrate the linear height. -/









/-! ### Brick 2: convex hull ⊆ triangleAffine image

The reverse inclusion `convexHull ℝ {a, b, c} ⊆ triangleAffine '' filled2Simplex`
combined with `triangleAffine_image_subset_convexHull` gives set equality. -/











/-! ### Brick 3: glue to `volume_convexHull_triangle`

The measure-theoretic bridge for Monsky's chapter 20:
`volume (convexHull ℝ {a, b, c}) = ENNReal.ofReal (realTriangleArea a b c)`. -/















/-! ### Packaged triangulation API

A `RealEqualAreaUnitSquareTriangulation α n` bundles the finite-vertex data
the Monsky frontier theorem
`no_odd_equalArea_realization_of_realSquareBoundaryVertexChain_area` consumes.
This is a refactoring layer: every hypothesis the existing theorem takes is
folded into a single named field, so downstream callers only need to construct
one structure instead of supplying twenty-plus arguments. -/





/-! ### Concrete witness: the diagonal split

The unit square can be split into two triangles of area 1/2 each by the main
diagonal — a constructive `RealEqualAreaUnitSquareTriangulation (Fin 4) 2`.
This is also a non-vacuity check on the packaged API: the structure can be
inhabited, just not for odd `n`. -/

namespace RealEqualAreaUnitSquareTriangulation





end RealEqualAreaUnitSquareTriangulation

end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20E2Frontier -/
section
set_option autoImplicit true


/-!
# Chapter 20 E2 frontier geometry

Auxiliary planar convex-geometry lemmas for the E2 incidence proof.
-/

namespace ProofsInTheBook.Chapter20

open scoped Topology

namespace Chapter20E2Frontier



























































end Chapter20E2Frontier



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20E2Frontier
-/
/- Source module: ProofsInTheBook.Chapter20E2Cover -/
section
set_option autoImplicit true


/-!
# Chapter 20 E2 cover lemmas

General connected-cover packaging for the local E2 incidence argument.
-/

namespace ProofsInTheBook.Chapter20

open scoped Topology
open Set

namespace Chapter20E2Cover













end Chapter20E2Cover



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20E2Cover
-/
/- Source module: ProofsInTheBook.Chapter20DissectionEngine -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — dissection engine (atomic incidence + reduction to E2)

This file defines a genuine `SquareDissection` (finite triangles, pairwise
disjoint interiors, union the unit square, equal area `1/n`), the atomic-segment
incidence built from it, and reduces Monsky's theorem to the single geometric
incidence fact **E2** (`atomicMult_even_of_interior` / `atomicMult_eq_one_of_boundary`).

The E2 statements are proved here as the main convex-geometry brick
(see `HANDOFF/CH20_E2_SPEC.md`).
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor
open scoped Topology





variable (D : SquareDissection)







































































































































































































































































/-! ### E2 — the geometric incidence core (the single heavy brick) -/





end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20Dissection -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — faithful dissection front end

`Chapter20.lean` proves Monsky's theorem **conditional on** the structure field
`RealEqualAreaUnitSquareTriangulation.hboundary`, which states that an unordered
*full* triangle edge `s(p, r) : Sym2 α` has odd triangle-multiplicity iff it lies
on the square boundary.  That is the *edge-to-edge* (simplicial) special case:
it fails for a genuine dissection in which a triangle side `p–r` is subdivided by
a "T-vertex" `m` belonging to neighbouring triangles, because then `s(p, r)` has
multiplicity `1` (odd) yet is interior.

Monsky's theorem is about **arbitrary** dissections.  The book (Aigner–Ziegler,
Ch. 20, Lemma 2) counts *atomic segments between consecutive vertices* and uses
"every red–green segment in the interior is counted twice".  This file builds
that faithful atomic-segment front end on top of the proved valuation / Sperner
engine in `Chapter20.lean`.

Sub-facts (book Lemma 2):
* **E2** each interior atomic segment lies on exactly two triangle boundaries,
  each boundary atomic segment on exactly one  *(the geometric core)*;
* **E3** on any straight side, the number of red–green atomic segments has the
  parity of `[endpoints are red&green]`, from the ≤2-colors-per-line corollary;
* **E5** the bottom side carries an odd number of red–green atomic segments and
  the other three sides carry none.

This file currently establishes the **≤2-colors-per-line corollary** to Lemma 1,
the foundation E3 rests on.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor





/-! ### E3 — per-side red–green parity (general, from ≤2 colors per line)

Along one straight side of a triangle the dissection vertices form a chain
`a :: middle ++ [b]` lying on a single line, so by the ≤2-colors corollary the
chain uses at most two of the three colors.  In that situation the number of
red–green atomic segments along the chain has exactly the parity of "the two
endpoints `a, b` form a red–green pair".  This upgrades the proved
`listRGTransitionCount_*` side lemmas (which fix the colors per side) to an
arbitrary side of an arbitrary triangle. -/



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20Dissection
-/
/- Source module: ProofsInTheBook.Chapter20Colors -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — collinear-list colour lemmas (E3 plumbing)

The ≤2-colours-per-line corollary (`not_trichromatic_of_collinear`) upgraded
from a single triple to a whole collinear list of points: a list in which every
triple is collinear omits at least one of the three Monsky colours, hence uses at
most two.  Combined with E3 (`odd_listRGTransitionCount_iff_endpoints`) this gives
the per-side red–green parity for an arbitrary subdivided triangle side.

Depends only on `Chapter20Dissection` (brick-1 + E3); independent of the geometric
`SquareDissection` definition, so it is stable while that is under construction.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor







end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20AtomicCount -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — abstract atomic double-count

The list-multiplicity analogue of the full-edge double-count
`sum_triangleLocalRGCount_mod_two_eq_oddEdgeRedGreenCount`.  Stated abstractly
for a finite family of edge-lists `f : Fin n → List (Sym2 V)`, so the dissection
engine instantiates it with `f := triAtomicEdges D`.  Engine-independent: depends
only on `Chapter20`.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable {V : Type*} [Fintype V] [DecidableEq V]













end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20SideGeom -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — side collinearity

The geometric fact behind the per-side E3 bridge: any three points lying on a
common segment `[P, Q]` are collinear, i.e. their signed double area vanishes.
Used to feed `exists_two_colors_of_collinear_list` for each subdivided triangle
side.  Engine-independent (raw points), instantiated later with vertex coords.
-/

namespace ProofsInTheBook.Chapter20



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20DissectionSperner -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — Sperner→contradiction spine

The engine-independent capstone spine: given a finite family of real triangles
each of area `1/n` (`n` odd) and the parity fact that the summed corner
red–green count is odd, Monsky's coloring forces a rainbow triangle whose area
cannot be `1/n` — contradiction.  This packages
`exists_trichromatic_of_odd_boundary` with
`not_real_triangleArea_eq_one_div_odd_of_trichromatic`, leaving the dissection
engine only to supply the parity hypothesis (`hparity`).

Depends only on `Chapter20`.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor



end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20DissectionEngine
import ProofsInTheBook.Chapter20E2Frontier
import ProofsInTheBook.Chapter20
-/
/- Source module: ProofsInTheBook.Chapter20E2Boundary -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — boundary atomic red-green parity

This file contains the boundary half of the atomic E2 bookkeeping: the
red-green atomic edges with odd atomic multiplicity are odd in number.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable (D : SquareDissection)















































































































































































































end ProofsInTheBook.Chapter20

end

/- Original source header (imports hoisted):
import ProofsInTheBook.Chapter20DissectionEngine
import ProofsInTheBook.Chapter20Colors
import ProofsInTheBook.Chapter20AtomicCount
import ProofsInTheBook.Chapter20SideGeom
import ProofsInTheBook.Chapter20DissectionSperner
import ProofsInTheBook.Chapter20E2Boundary
-/
/- Source module: ProofsInTheBook.Chapter20DissectionFinal -/
section
set_option autoImplicit true


/-!
# Chapter 20 (Monsky) — final assembly

Wires the verified combinatorial layer to the geometric core (E2):
* per-side E3 bridge: along each subdivided triangle side the red-green atomic
  count has the parity of the side's endpoint colours (collinear ⇒ ≤2 colours);
* per-triangle: `listEdgeRGCount (triAtomicEdges i) ≡ triangleLocalRGCount` (mod 2);
* the atomic double-count + E2 turn the summed corner parity into the
  square-boundary atomic parity;
* the boundary organization (odd) + the Sperner spine close the chapter.

`monsky_dissection` is `False`-from-an-odd-equal-area-dissection, conditional only
on the geometric E2 (proved in the engine) and the boundary organization lemma.
-/

namespace ProofsInTheBook.Chapter20

open MonskyColor

variable (D : SquareDissection)













end ProofsInTheBook.Chapter20

end


set_option autoImplicit true
open ProofsInTheBook.Chapter20
open MonskyColor

theorem solution
    {n : ℕ} (hn : Odd n) (tri : Fin n → (ℝ × ℝ) × (ℝ × ℝ) × (ℝ × ℝ))
    (harea : ∀ i, realTriangleArea (tri i).1 (tri i).2.1 (tri i).2.2 =
      (((1 : ℚ) / n : ℚ) : ℝ))
    (hodd : Odd (∑ i : Fin n, triangleLocalRGCount
      (realTwoAdicColor (tri i).1, realTwoAdicColor (tri i).2.1,
        realTwoAdicColor (tri i).2.2))) :
    False := by
  classical
  set tc : Fin n → MonskyColor × MonskyColor × MonskyColor :=
    fun i => (realTwoAdicColor (tri i).1, realTwoAdicColor (tri i).2.1,
      realTwoAdicColor (tri i).2.2) with htc
  set total : ℕ := ∑ i : Fin n, triangleLocalRGCount (tc i) with htotaldef
  -- `exists_trichromatic_of_odd_boundary` with boundary count = total (parity trivial)
  have htotal : total = ∑ i : Fin n,
      ((if RedGreenEdge (tc i).1 (tc i).2.1 then 1 else 0) +
       (if RedGreenEdge (tc i).2.1 (tc i).2.2 then 1 else 0) +
       (if RedGreenEdge (tc i).2.2 (tc i).1 then 1 else 0)) := by
    rw [htotaldef]; rfl
  obtain ⟨i, htri⟩ := exists_trichromatic_of_odd_boundary n tc total total htotal rfl
    (by rw [htotaldef]; exact hodd)
  exact not_real_triangleArea_eq_one_div_odd_of_trichromatic hn htri (harea i)
