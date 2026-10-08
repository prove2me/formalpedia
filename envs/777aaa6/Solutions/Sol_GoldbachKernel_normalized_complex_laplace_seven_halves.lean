-- Prove2me | solution 1 for GoldbachKernel_normalized_complex_laplace_seven_halves
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T12:00:41.105286+00:00
-- url     : https://prove2.me/submissions/ba54c8a1-7596-45d3-ad1b-24c0a09c5254

import Mathlib
import Theorems.Thm_GoldbachKernel_polynomial_laplace_right_half_plane_nonneg
import Theorems.Thm_GoldbachKernel_normalized_complex_laplace_tail_eight
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

-- Dependency: Verification.Check_GoldbachRationalIntervals

set_option autoImplicit false

namespace GoldbachInterval

structure Box where
  lo : ℚ
  hi : ℚ

def Contains (a : Box) (x : ℝ) : Prop := (a.lo:ℝ) ≤ x ∧ x ≤ (a.hi:ℝ)

def down (S : ℕ) (q : ℚ) : ℚ := (⌊q*(S:ℚ)⌋:ℚ)/(S:ℚ)
def up (S : ℕ) (q : ℚ) : ℚ := -down S (-q)

theorem down_le (S : ℕ) (hS : 0 < S) (q : ℚ) : (down S q:ℝ) ≤ (q:ℝ) := by
  have hs : 0 < (S:ℝ) := by exact_mod_cast hS
  have hf : (⌊q*(S:ℚ)⌋:ℚ) ≤ q*(S:ℚ) := Int.floor_le _
  have hr : (⌊q*(S:ℚ)⌋:ℝ) ≤ (q:ℝ)*(S:ℝ) := by exact_mod_cast hf
  unfold down
  push_cast
  exact (div_le_iff₀ hs).mpr hr

theorem le_up (S : ℕ) (hS : 0 < S) (q : ℚ) : (q:ℝ) ≤ (up S q:ℝ) := by
  simpa only [up, Rat.cast_neg, neg_neg] using neg_le_neg (down_le S hS (-q))

def point (S : ℕ) (q : ℚ) : Box := ⟨down S q, up S q⟩
def add (a b : Box) : Box := ⟨a.lo+b.lo, a.hi+b.hi⟩
def neg (a : Box) : Box := ⟨-a.hi, -a.lo⟩
def sub (a b : Box) : Box := add a (neg b)

theorem point_contains (S : ℕ) (hS : 0 < S) (q : ℚ) : Contains (point S q) (q:ℝ) :=
  ⟨down_le S hS q, le_up S hS q⟩

theorem add_contains (a b : Box) (x y : ℝ) (hx : Contains a x) (hy : Contains b y) :
    Contains (add a b) (x+y) := by
  constructor <;> dsimp [add] <;> push_cast
  · exact add_le_add hx.1 hy.1
  · exact add_le_add hx.2 hy.2

theorem neg_contains (a : Box) (x : ℝ) (hx : Contains a x) : Contains (neg a) (-x) := by
  constructor <;> dsimp [neg] <;> push_cast
  · exact neg_le_neg hx.2
  · exact neg_le_neg hx.1

theorem sub_contains (a b : Box) (x y : ℝ) (hx : Contains a x) (hy : Contains b y) :
    Contains (sub a b) (x-y) := by
  exact add_contains a (neg b) x (-y) hx (neg_contains b y hy)

private theorem Verification_Check_GoldbachRationalIntervals_private_linear_bounds (a l u x : ℝ) (hx : l ≤ x ∧ x ≤ u) :
    min (a*l) (a*u) ≤ a*x ∧ a*x ≤ max (a*l) (a*u) := by
  by_cases ha : 0 ≤ a
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hx.1 ha),
      (mul_le_mul_of_nonneg_left hx.2 ha).trans (le_max_right _ _)⟩
  · have hn : a ≤ 0 := le_of_not_ge ha
    exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hx.2 hn),
      (mul_le_mul_of_nonpos_left hx.1 hn).trans (le_max_left _ _)⟩

theorem four_corner_bounds (l u v w x y : ℝ) (hx : l ≤ x ∧ x ≤ u)
    (hy : v ≤ y ∧ y ≤ w) :
    min (min (l*v) (l*w)) (min (u*v) (u*w)) ≤ x*y ∧
      x*y ≤ max (max (l*v) (l*w)) (max (u*v) (u*w)) := by
  have h₁ := Verification_Check_GoldbachRationalIntervals_private_linear_bounds y l u x hx
  have h₂ := Verification_Check_GoldbachRationalIntervals_private_linear_bounds l v w y hy
  have h₃ := Verification_Check_GoldbachRationalIntervals_private_linear_bounds u v w y hy
  constructor
  · have h := (min_le_min h₂.1 h₃.1).trans (by simpa only [mul_comm] using h₁.1)
    exact h
  · have h := (by simpa only [mul_comm] using h₁.2 : x*y ≤ max (l*y) (u*y)).trans
      (max_le_max h₂.2 h₃.2)
    exact h

def mul (S : ℕ) (a b : Box) : Box :=
  ⟨down S (min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))),
   up S (max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi)))⟩

theorem mul_contains (S : ℕ) (hS : 0 < S) (a b : Box) (x y : ℝ)
    (hx : Contains a x) (hy : Contains b y) : Contains (mul S a b) (x*y) := by
  have h := four_corner_bounds (a.lo:ℝ) a.hi b.lo b.hi x y hx hy
  constructor
  · apply (down_le S hS _).trans
    push_cast
    exact h.1
  · apply h.2.trans
    convert le_up S hS (max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi))) using 1
    push_cast
    rfl

def square (S : ℕ) (a : Box) : Box :=
  ⟨down S (if a.lo ≤ 0 ∧ 0 ≤ a.hi then 0 else min (a.lo^2) (a.hi^2)),
   up S (max (a.lo^2) (a.hi^2))⟩

theorem square_contains (S : ℕ) (hS : 0 < S) (a : Box) (x : ℝ)
    (hx : Contains a x) : Contains (square S a) (x^2) := by
  have hupper : x^2 ≤ max ((a.lo:ℝ)^2) ((a.hi:ℝ)^2) := by
    by_cases hp : 0 ≤ x
    · have hu : x^2 ≤ (a.hi:ℝ)^2 := by nlinarith [hx.2]
      exact hu.trans (le_max_right _ _)
    · have hl : x^2 ≤ (a.lo:ℝ)^2 := by nlinarith [hx.1]
      exact hl.trans (le_max_left _ _)
  constructor
  · apply (down_le S hS _).trans
    by_cases hc : a.lo ≤ 0 ∧ 0 ≤ a.hi
    · simp only [if_pos hc, Rat.cast_zero]
      exact sq_nonneg x
    · simp only [if_neg hc]
      push_cast
      by_cases hp : (0:ℝ) ≤ a.lo
      · have hl : (a.lo:ℝ)^2 ≤ x^2 := by nlinarith [hx.1]
        exact (min_le_left _ _).trans hl
      · have hu : (a.hi:ℝ) ≤ 0 := by
          have hlo : ¬ (0:ℚ) ≤ a.lo := by exact_mod_cast hp
          have hh : ¬ (0:ℚ) ≤ a.hi := by
            intro hhi
            apply hc
            exact ⟨(le_of_not_ge hlo),hhi⟩
          exact_mod_cast le_of_not_ge hh
        have hl : (a.hi:ℝ)^2 ≤ x^2 := by nlinarith [hx.2]
        exact (min_le_right _ _).trans hl
  · have h := le_up S hS (max (a.lo^2) (a.hi^2))
    have hcast : ((max (a.lo^2) (a.hi^2):ℚ):ℝ) = max ((a.lo:ℝ)^2) ((a.hi:ℝ)^2) := by push_cast; rfl
    rw [hcast] at h
    exact hupper.trans h

def reciprocal (S : ℕ) (a : Box) : Box := ⟨down S (1/a.hi), up S (1/a.lo)⟩

theorem reciprocal_contains (S : ℕ) (hS : 0 < S) (a : Box) (x : ℝ)
    (hpos : (0:ℝ) < a.lo) (hx : Contains a x) :
    Contains (reciprocal S a) (1/x) := by
  have hxpos : 0 < x := hpos.trans_le hx.1
  constructor
  · apply (down_le S hS _).trans
    push_cast
    exact one_div_le_one_div_of_le hxpos hx.2
  · apply (one_div_le_one_div_of_le hpos hx.1).trans
    convert le_up S hS (1/a.lo) using 1
    push_cast
    rfl


def divide (S : ℕ) (a b : Box) : Box := mul S a (reciprocal S b)

theorem divide_contains (S : ℕ) (hS : 0 < S) (a b : Box) (x y : ℝ)
    (hx : Contains a x) (hy : Contains b y) (hpos : (0:ℝ) < b.lo) :
    Contains (divide S a b) (x/y) := by
  simpa only [divide, div_eq_mul_inv, one_div, one_mul] using
    mul_contains S hS a (reciprocal S b) x (1/y) hx (reciprocal_contains S hS b y hpos hy)

def power (S : ℕ) (a : Box) : ℕ → Box
  | 0 => point S 1
  | n+1 => mul S a (power S a n)

def horner (S : ℕ) (coefficients : List ℚ) (x : Box) : Box :=
  coefficients.foldr (fun coefficient rest => add (point S coefficient) (mul S x rest)) (point S 0)

theorem horner_contains (S : ℕ) (hS : 0 < S) (coefficients : List ℚ) (a : Box) (x : ℝ)
    (hx : Contains a x) : Contains (horner S coefficients a)
      (coefficients.foldr (fun (coefficient : ℚ) (rest : ℝ) => (coefficient:ℝ)+x*rest) 0) := by
  induction coefficients with
  | nil => simpa [horner] using point_contains S hS 0
  | cons c cs ih =>
    exact add_contains (point S c) (mul S a (horner S cs a)) c
      (x*(cs.foldr (fun (coefficient : ℚ) (rest : ℝ) => (coefficient:ℝ)+x*rest) 0))
      (point_contains S hS c) (mul_contains S hS a (horner S cs a) x _ hx ih)

def inflate (S : ℕ) (a : Box) (error : ℚ) : Box :=
  ⟨a.lo-up S error, a.hi+up S error⟩

theorem inflate_contains (S : ℕ) (hS : 0 < S) (a : Box) (x y : ℝ) (error : ℚ)
    (hx : Contains a x) (herror : |y-x| ≤ (error:ℝ)) :
    Contains (inflate S a error) y := by
  have he := abs_le.mp herror
  have hu := le_up S hS error
  constructor <;> dsimp [inflate] <;> push_cast
  · linarith [hx.1, he.1]
  · linarith [hx.2, he.2]


theorem horner_real_eq_power_sum (coefficients : List ℚ) (x : ℝ) :
    coefficients.foldr (fun (coefficient : ℚ) (rest : ℝ) => (coefficient:ℝ)+x*rest) 0 =
      ∑ k ∈ Finset.range coefficients.length,
        (((coefficients[k]?).getD 0:ℚ):ℝ)*x^k := by
  induction coefficients with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldr_cons, List.length_cons, Finset.sum_range_succ',
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, pow_zero, mul_one]
    rw [ih, Finset.mul_sum, add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_succ]
    ring

theorem horner_power_sum_contains (S : ℕ) (hS : 0 < S) (coefficients : List ℚ)
    (a : Box) (x : ℝ) (hx : Contains a x) : Contains (horner S coefficients a)
      (∑ k ∈ Finset.range coefficients.length,
        (((coefficients[k]?).getD 0:ℚ):ℝ)*x^k) := by
  rw [← horner_real_eq_power_sum]
  exact horner_contains S hS coefficients a x hx


theorem horner_generated_coefficients_contains (S : ℕ) (hS : 0 < S)
    (n : ℕ) (coefficient : ℕ → ℚ) (a : Box) (x : ℝ) (hx : Contains a x) :
    Contains (horner S ((List.range n).map coefficient) a)
      (∑ k ∈ Finset.range n, (coefficient k:ℝ)*x^k) := by
  have h := horner_power_sum_contains S hS ((List.range n).map coefficient) a x hx
  simp only [List.length_map, List.length_range] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n := Finset.mem_range.mp hk
  simp [hk']


end GoldbachInterval

-- Dependency: Verification.Check_GoldbachIntegerIntervals

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval.Integer

structure Box where
  lo : ℤ
  hi : ℤ

def lift (S : ℕ) (a : Box) : GoldbachInterval.Box :=
  ⟨(a.lo:ℚ)/(S:ℚ),(a.hi:ℚ)/(S:ℚ)⟩
def point (S : ℕ) (q : ℚ) : Box := ⟨⌊q*(S:ℚ)⌋,-⌊-q*(S:ℚ)⌋⟩
def add (a b : Box) : Box := ⟨a.lo+b.lo,a.hi+b.hi⟩
def neg (a : Box) : Box := ⟨-a.hi,-a.lo⟩
def sub (a b : Box) : Box := add a (neg b)
def floorDiv (S : ℕ) (n : ℤ) : ℤ := n/(S:ℤ)
def ceilDiv (S : ℕ) (n : ℤ) : ℤ := -((-n)/(S:ℤ))
def mul (S : ℕ) (a b : Box) : Box :=
  ⟨floorDiv S (min (min (a.lo*b.lo) (a.lo*b.hi)) (min (a.hi*b.lo) (a.hi*b.hi))),
   ceilDiv S (max (max (a.lo*b.lo) (a.lo*b.hi)) (max (a.hi*b.lo) (a.hi*b.hi)))⟩

theorem lift_point (S : ℕ) (q : ℚ) : lift S (point S q) = GoldbachInterval.point S q := by
  simp only [lift, point, GoldbachInterval.point, GoldbachInterval.down,
    GoldbachInterval.up, Int.cast_neg, neg_mul, neg_div]

theorem lift_add (S : ℕ) (a b : Box) :
    lift S (add a b) = GoldbachInterval.add (lift S a) (lift S b) := by
  unfold lift add GoldbachInterval.add
  push_cast
  simp only [add_div]

theorem lift_neg (S : ℕ) (a : Box) :
    lift S (neg a) = GoldbachInterval.neg (lift S a) := by
  unfold lift neg GoldbachInterval.neg
  simp only [Int.cast_neg, neg_div]

theorem lift_sub (S : ℕ) (a b : Box) :
    lift S (sub a b) = GoldbachInterval.sub (lift S a) (lift S b) := by
  simp only [sub, GoldbachInterval.sub, lift_add, lift_neg]

theorem down_grid_product (S : ℕ) (hS : 0 < S) (n : ℤ) :
    GoldbachInterval.down S ((n:ℚ)/(S:ℚ)^2) = (floorDiv S n:ℚ)/(S:ℚ) := by
  have hs : (S:ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hS)
  have h : (n:ℚ)/(S:ℚ)^2*(S:ℚ) = (n:ℚ)/(S:ℚ) := by field_simp
  unfold GoldbachInterval.down floorDiv
  rw [h, Rat.floor_intCast_div_natCast]

theorem up_grid_product (S : ℕ) (hS : 0 < S) (n : ℤ) :
    GoldbachInterval.up S ((n:ℚ)/(S:ℚ)^2) = (ceilDiv S n:ℚ)/(S:ℚ) := by
  unfold GoldbachInterval.up ceilDiv
  have h : -((n:ℚ)/(S:ℚ)^2) = ((-n:ℤ):ℚ)/(S:ℚ)^2 := by push_cast; ring
  rw [h, down_grid_product S hS]
  simp only [floorDiv, Int.cast_neg, neg_div]

theorem lift_mul (S : ℕ) (hS : 0 < S) (a b : Box) :
    lift S (mul S a b) = GoldbachInterval.mul S (lift S a) (lift S b) := by
  have hsq : (0:ℚ) ≤ (S:ℚ)^2 := sq_nonneg _
  have hc (x y : ℤ) : ((x:ℚ)/(S:ℚ))*((y:ℚ)/(S:ℚ)) = ((x*y:ℤ):ℚ)/(S:ℚ)^2 := by
    push_cast
    rw [div_mul_div_comm]
    ring
  unfold lift mul GoldbachInterval.mul
  simp only [hc]
  simp only [min_div_div_right hsq, max_div_div_right hsq]
  simp only [← Int.cast_min, ← Int.cast_max]
  rw [down_grid_product S hS, up_grid_product S hS]


end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachIntegerIntervalEvaluation

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval.Integer

def floorRatio (n d : ℤ) : ℤ := if 0 ≤ d then n/d else (-n)/(-d)
def ceilRatio (n d : ℤ) : ℤ := -floorRatio (-n) d

theorem floor_ratio (n d : ℤ) : ⌊((n:ℚ)/(d:ℚ))⌋ = floorRatio n d := by
  unfold floorRatio
  by_cases hd : 0 ≤ d
  · rw [if_pos hd]
    simpa only [Int.floor_intCast] using Int.floor_div_cast_of_nonneg hd (n:ℚ)
  · rw [if_neg hd]
    have hd' : 0 ≤ -d := by omega
    have h := Int.floor_div_cast_of_nonneg hd' ((-n:ℤ):ℚ)
    simpa using h

def reciprocal (S : ℕ) (a : Box) : Box :=
  ⟨floorRatio ((S:ℤ)^2) a.hi,ceilRatio ((S:ℤ)^2) a.lo⟩
def divide (S : ℕ) (a b : Box) : Box := mul S a (reciprocal S b)

theorem down_grid_reciprocal (S : ℕ) (d : ℤ) :
    GoldbachInterval.down S ((S:ℚ)/(d:ℚ)) =
      (floorRatio ((S:ℤ)^2) d:ℚ)/(S:ℚ) := by
  have h : (S:ℚ)/(d:ℚ)*(S:ℚ) = (((S:ℤ)^2:ℤ):ℚ)/(d:ℚ) := by push_cast; ring
  unfold GoldbachInterval.down
  rw [h,floor_ratio]

theorem up_grid_reciprocal (S : ℕ) (d : ℤ) :
    GoldbachInterval.up S ((S:ℚ)/(d:ℚ)) =
      (ceilRatio ((S:ℤ)^2) d:ℚ)/(S:ℚ) := by
  have h : -((S:ℚ)/(d:ℚ))*(S:ℚ) = ((-((S:ℤ)^2):ℤ):ℚ)/(d:ℚ) := by push_cast; ring
  unfold GoldbachInterval.up GoldbachInterval.down ceilRatio
  rw [h,floor_ratio]
  simp only [Int.cast_neg,neg_div]

theorem lift_reciprocal (S : ℕ) (a : Box) :
    lift S (reciprocal S a) = GoldbachInterval.reciprocal S (lift S a) := by
  unfold lift reciprocal GoldbachInterval.reciprocal
  rw [one_div_div,one_div_div,down_grid_reciprocal,up_grid_reciprocal]

theorem lift_divide (S : ℕ) (hS : 0 < S) (a b : Box) :
    lift S (divide S a b) = GoldbachInterval.divide S (lift S a) (lift S b) := by
  simp only [divide,GoldbachInterval.divide,lift_mul S hS,lift_reciprocal]

def power (S : ℕ) (a : Box) : ℕ → Box
  | 0 => point S 1
  | n+1 => mul S a (power S a n)

def horner (S : ℕ) : List ℚ → Box → Box
  | [],_ => point S 0
  | c::cs,a => add (point S c) (mul S a (horner S cs a))

theorem lift_horner (S : ℕ) (hS : 0 < S) (coefficients : List ℚ) (a : Box) :
    lift S (horner S coefficients a) = GoldbachInterval.horner S coefficients (lift S a) := by
  induction coefficients with
  | nil => exact lift_point S 0
  | cons c cs ih =>
    change lift S (add (point S c) (mul S a (horner S cs a))) =
      GoldbachInterval.add (GoldbachInterval.point S c)
        (GoldbachInterval.mul S (lift S a) (GoldbachInterval.horner S cs (lift S a)))
    rw [lift_add,lift_point,lift_mul S hS,ih]

def inflate (S : ℕ) (a : Box) (error : ℚ) : Box :=
  ⟨a.lo-(point S error).hi,a.hi+(point S error).hi⟩

theorem lift_inflate (S : ℕ) (a : Box) (error : ℚ) :
    lift S (inflate S a error) = GoldbachInterval.inflate S (lift S a) error := by
  have h : (((point S error).hi:ℤ):ℚ)/(S:ℚ) = GoldbachInterval.up S error :=
    congrArg GoldbachInterval.Box.hi (lift_point S error)
  simp only [lift,inflate,GoldbachInterval.inflate,Int.cast_sub,Int.cast_add,sub_div,add_div,h]


end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachIntegerSquares

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval.Integer

def square (S : ℕ) (a : Box) : Box :=
  ⟨floorDiv S (if a.lo ≤ 0 ∧ 0 ≤ a.hi then 0 else min (a.lo^2) (a.hi^2)),
   ceilDiv S (max (a.lo^2) (a.hi^2))⟩

theorem lift_square (S : ℕ) (hS : 0 < S) (a : Box) :
    lift S (square S a) = GoldbachInterval.square S (lift S a) := by
  have hs : (0:ℚ) < (S:ℚ) := by exact_mod_cast hS
  have hsq : (0:ℚ) ≤ (S:ℚ)^2 := sq_nonneg _
  have hp (n : ℤ) : ((n:ℚ)/(S:ℚ))^2 = ((n^2:ℤ):ℚ)/(S:ℚ)^2 := by
    push_cast
    rw [div_pow]
  have hc : ((a.lo:ℚ)/(S:ℚ) ≤ 0 ∧ 0 ≤ (a.hi:ℚ)/(S:ℚ)) ↔
      (a.lo ≤ 0 ∧ 0 ≤ a.hi) := by
    simp only [div_le_iff₀ hs,le_div_iff₀ hs,zero_mul,Int.cast_nonpos] <;> norm_cast
  unfold lift square GoldbachInterval.square
  simp only [hp,min_div_div_right hsq,max_div_div_right hsq,← Int.cast_min,← Int.cast_max]
  by_cases hspan : a.lo ≤ 0 ∧ 0 ≤ a.hi
  · have hspan' := hc.mpr hspan
    simp only [if_pos hspan,if_pos hspan']
    rw [up_grid_product S hS]
    simp [floorDiv,GoldbachInterval.down]
  · have hspan' : ¬ ((a.lo:ℚ)/(S:ℚ) ≤ 0 ∧ 0 ≤ (a.hi:ℚ)/(S:ℚ)) :=
      fun h => hspan (hc.mp h)
    simp only [if_neg hspan,if_neg hspan']
    rw [down_grid_product S hS,up_grid_product S hS]


end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachComplexIntervals

set_option autoImplicit false

namespace GoldbachInterval

structure ComplexBox where
  re : Box
  im : Box

def ContainsComplex (a : ComplexBox) (z : ℂ) : Prop :=
  Contains a.re z.re ∧ Contains a.im z.im

def realPoint (S : ℕ) (q : ℚ) : ComplexBox := ⟨point S q, point S 0⟩
def complexAdd (a b : ComplexBox) : ComplexBox := ⟨add a.re b.re, add a.im b.im⟩
def complexNeg (a : ComplexBox) : ComplexBox := ⟨neg a.re, neg a.im⟩
def complexSub (a b : ComplexBox) : ComplexBox := complexAdd a (complexNeg b)
def complexMul (S : ℕ) (a b : ComplexBox) : ComplexBox :=
  ⟨sub (mul S a.re b.re) (mul S a.im b.im),
   add (mul S a.re b.im) (mul S a.im b.re)⟩

theorem realPoint_contains (S : ℕ) (hS : 0 < S) (q : ℚ) :
    ContainsComplex (realPoint S q) ((q:ℝ):ℂ) := by
  constructor
  · simpa only [Complex.ofReal_re] using point_contains S hS q
  · simpa only [Complex.ofReal_im, Rat.cast_zero] using point_contains S hS 0

theorem complexAdd_contains (a b : ComplexBox) (z w : ℂ)
    (hz : ContainsComplex a z) (hw : ContainsComplex b w) :
    ContainsComplex (complexAdd a b) (z+w) := by
  exact ⟨add_contains a.re b.re z.re w.re hz.1 hw.1,
    add_contains a.im b.im z.im w.im hz.2 hw.2⟩

theorem complexMul_contains (S : ℕ) (hS : 0 < S) (a b : ComplexBox) (z w : ℂ)
    (hz : ContainsComplex a z) (hw : ContainsComplex b w) :
    ContainsComplex (complexMul S a b) (z*w) := by
  constructor
  · exact sub_contains _ _ _ _
      (mul_contains S hS a.re b.re z.re w.re hz.1 hw.1)
      (mul_contains S hS a.im b.im z.im w.im hz.2 hw.2)
  · exact add_contains _ _ _ _
      (mul_contains S hS a.re b.im z.re w.im hz.1 hw.2)
      (mul_contains S hS a.im b.re z.im w.re hz.2 hw.1)

def complexPower (S : ℕ) (a : ComplexBox) : ℕ → ComplexBox
  | 0 => realPoint S 1
  | n+1 => complexMul S a (complexPower S a n)

theorem complexPower_contains (S : ℕ) (hS : 0 < S) (a : ComplexBox) (z : ℂ)
    (hz : ContainsComplex a z) (n : ℕ) : ContainsComplex (complexPower S a n) (z^n) := by
  induction n with
  | zero => simpa [complexPower] using realPoint_contains S hS 1
  | succ n ih =>
    simpa only [complexPower, pow_succ, mul_comm] using
      complexMul_contains S hS a (complexPower S a n) z (z^n) hz ih

def squaredNorm (S : ℕ) (a : ComplexBox) : Box := add (square S a.re) (square S a.im)
def complexInverse (S : ℕ) (a : ComplexBox) : ComplexBox :=
  ⟨divide S a.re (squaredNorm S a), divide S (neg a.im) (squaredNorm S a)⟩

theorem squaredNorm_contains (S : ℕ) (hS : 0 < S) (a : ComplexBox) (z : ℂ)
    (hz : ContainsComplex a z) : Contains (squaredNorm S a) (Complex.normSq z) := by
  simpa only [squaredNorm, Complex.normSq_apply, pow_two] using add_contains _ _ _ _
    (square_contains S hS a.re z.re hz.1) (square_contains S hS a.im z.im hz.2)

theorem complexInverse_contains (S : ℕ) (hS : 0 < S) (a : ComplexBox) (z : ℂ)
    (hz : ContainsComplex a z) (hpositive : (0:ℝ) < (squaredNorm S a).lo) :
    ContainsComplex (complexInverse S a) z⁻¹ := by
  have hden := squaredNorm_contains S hS a z hz
  constructor
  · simpa only [Complex.inv_re] using divide_contains S hS a.re (squaredNorm S a)
      z.re (Complex.normSq z) hz.1 hden hpositive
  · simpa only [Complex.inv_im] using divide_contains S hS (neg a.im) (squaredNorm S a)
      (-z.im) (Complex.normSq z) (neg_contains a.im z.im hz.2) hden hpositive


end GoldbachInterval

-- Dependency: Verification.Check_GoldbachComplexLaplaceClosedForm

open MeasureTheory
set_option autoImplicit false

-- Local prerequisite for a future all-frequency comparison; no inequality is asserted.
theorem goldbach_complex_laplace_closed_form (z : ℂ) (hz : z ≠ 0) :
    (∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-z*(u:ℂ))) =
      (16*z^5-40*z^3+60*z^2-60+60*Complex.exp (-2*z)*(z+1)^2)/(15*z^6) := by
  let a0 : ℂ := -16/(15*z)+8/(3*z^3)-4/z^4+4/z^6
  let a1 : ℂ := 8/(3*z^2)-4/z^3+4/z^5
  let a2 : ℂ := 4/(3*z)-2/z^2+2/z^4
  let a3 : ℂ := -2/(3*z)+2/(3*z^3)
  let a4 : ℂ := 1/(6*z^2)
  let a5 : ℂ := 1/(30*z)
  let Q : ℂ → ℂ := fun u => a0+a1*u+a2*u^2+a3*u^3+a4*u^4+a5*u^5
  have hQ (u : ℂ) : HasDerivAt Q (a1+2*a2*u+3*a3*u^2+4*a4*u^3+5*a5*u^4) u := by
    convert (((((hasDerivAt_const u a0).add ((hasDerivAt_id u).const_mul a1)).add
      ((hasDerivAt_pow 2 u).const_mul a2)).add ((hasDerivAt_pow 3 u).const_mul a3)).add
      ((hasDerivAt_pow 4 u).const_mul a4)).add ((hasDerivAt_pow 5 u).const_mul a5) using 1
    dsimp [Q]
    ring
  have hd (u : ℂ) : HasDerivAt (fun v => Q v*Complex.exp (-z*v))
      (((2-u)^3*(4+6*u+u^2)/30)*Complex.exp (-z*u)) u := by
    have he := (Complex.hasDerivAt_exp (-z*u)).comp u ((hasDerivAt_id u).const_mul (-z))
    convert (hQ u).mul he using 1
    dsimp [Q,a0,a1,a2,a3,a4,a5]
    field_simp
    ring
  have hreal (u : ℝ) : HasDerivAt (fun v : ℝ => Q (v:ℂ)*Complex.exp (-z*(v:ℂ)))
      (((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*Complex.exp (-z*(u:ℂ))) u := by
    simpa only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_ofNat] using
      (hd (u:ℂ)).comp_ofReal
  have hint : IntervalIntegrable
      (fun u : ℝ => (((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*Complex.exp (-z*(u:ℂ))))
      volume 0 2 := by
    have hcont : Continuous
        (fun u : ℝ => (((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*Complex.exp (-z*(u:ℂ)))) := by
      fun_prop
    exact hcont.intervalIntegrable (μ := volume) 0 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hreal u) hint]
  dsimp [Q,a0,a1,a2,a3,a4,a5]
  have he : -z*2 = -2*z := by ring
  norm_num only [Complex.ofReal_ofNat]
  rw [he]
  norm_num
  field_simp
  ring


-- The rational expression above has an apparent singularity; handle its origin separately.
private noncomputable def Verification_Check_GoldbachComplexLaplaceClosedForm_private_goldbachG (z : ℂ) : ℂ :=
  ∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*Complex.exp (-z*(u:ℂ))

open MeasureTheory Set Filter
open scoped Topology
set_option autoImplicit false

noncomputable def goldbachWeightedZ (m : ℕ) (r : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*u^m*Real.exp (-r*u)

open MeasureTheory
set_option autoImplicit false

noncomputable def goldbachMiddleG (z : ℂ) : ℂ :=
  (16/15:ℂ)*z⁻¹-(8/3:ℂ)*(z⁻¹)^3+4*(z⁻¹)^4-4*(z⁻¹)^6+
    Complex.exp (-2*z)*(4*(z⁻¹)^4+8*(z⁻¹)^5+4*(z⁻¹)^6)

noncomputable def goldbachMiddleG1 (z : ℂ) : ℂ :=
  -(16/15:ℂ)*(z⁻¹)^2+8*(z⁻¹)^4-16*(z⁻¹)^5+24*(z⁻¹)^7+
    Complex.exp (-2*z)*(-8*(z⁻¹)^4-32*(z⁻¹)^5-48*(z⁻¹)^6-24*(z⁻¹)^7)

noncomputable def goldbachMiddleG2 (z : ℂ) : ℂ :=
  (32/15:ℂ)*(z⁻¹)^3-32*(z⁻¹)^5+80*(z⁻¹)^6-168*(z⁻¹)^8+
    Complex.exp (-2*z)*(16*(z⁻¹)^4+96*(z⁻¹)^5+256*(z⁻¹)^6+
      336*(z⁻¹)^7+168*(z⁻¹)^8)

theorem goldbach_middle_complex_closed_form (z : ℂ) (hz : z ≠ 0) :
    (∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-z*(u:ℂ))) = goldbachMiddleG z := by
  rw [goldbach_complex_laplace_closed_form z hz]
  unfold goldbachMiddleG
  field_simp
  ring

noncomputable def goldbachMiddleH (r t : ℝ) : ℝ :=
  goldbachWeightedZ 0 r*(goldbachMiddleG1 ((r:ℂ)+(t:ℂ)*Complex.I)).re+
    goldbachWeightedZ 1 r*(goldbachMiddleG ((r:ℂ)+(t:ℂ)*Complex.I)).re

set_option autoImplicit false

namespace GoldbachInterval

def complexTerm (S : ℕ) (a : ComplexBox) (term : ℚ×ℕ) : ComplexBox :=
  complexMul S (complexPower S a term.2) (realPoint S term.1)

def complexTerms (S : ℕ) (a : ComplexBox) (terms : List (ℚ×ℕ)) : ComplexBox :=
  terms.foldl (fun acc term => complexAdd acc (complexTerm S a term)) (realPoint S 0)

private theorem Verification_Check_GoldbachTransformEnclosures_private_complexTermsFold_contains (S : ℕ) (hS : 0 < S) (a : ComplexBox) (z : ℂ)
    (hz : ContainsComplex a z) (terms : List (ℚ×ℕ)) (initial : ComplexBox) (value : ℂ)
    (hinitial : ContainsComplex initial value) :
    ContainsComplex
      (terms.foldl (fun acc term => complexAdd acc (complexTerm S a term)) initial)
      (terms.foldl (fun (acc : ℂ) (term : ℚ×ℕ) => acc+z^term.2*((term.1:ℝ):ℂ)) value) := by
  induction terms generalizing initial value with
  | nil => exact hinitial
  | cons term terms ih =>
    exact ih _ _ (complexAdd_contains _ _ _ _ hinitial
      (complexMul_contains S hS _ _ _ _
        (complexPower_contains S hS a z hz term.2) (realPoint_contains S hS term.1)))

theorem complexTerms_contains (S : ℕ) (hS : 0 < S) (a : ComplexBox) (z : ℂ)
    (hz : ContainsComplex a z) (terms : List (ℚ×ℕ)) :
    ContainsComplex (complexTerms S a terms)
      (terms.foldl (fun (acc : ℂ) (term : ℚ×ℕ) => acc+z^term.2*((term.1:ℝ):ℂ)) 0) := by
  simpa only [complexTerms, Rat.cast_zero, Complex.ofReal_zero] using
    Verification_Check_GoldbachTransformEnclosures_private_complexTermsFold_contains S hS a z hz terms (realPoint S 0) 0
      (by simpa only [Rat.cast_zero, Complex.ofReal_zero] using realPoint_contains S hS 0)

def realScale (S : ℕ) (a : ComplexBox) (b : Box) : ComplexBox :=
  ⟨mul S a.re b, mul S a.im b⟩

theorem realScale_contains (S : ℕ) (hS : 0 < S) (a : ComplexBox) (b : Box)
    (z : ℂ) (r : ℝ) (hz : ContainsComplex a z) (hr : Contains b r) :
    ContainsComplex (realScale S a b) (z*(r:ℂ)) := by
  constructor
  · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using
      mul_contains S hS a.re b z.re r hz.1 hr
  · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] using
      mul_contains S hS a.im b z.im r hz.2 hr

def transformP : List (ℚ×ℕ) := [(16/15,1),(-8/3,3),(4,4),(-4,6)]
def transformQ : List (ℚ×ℕ) := [(4,4),(8,5),(4,6)]

def transformEnclosure (S : ℕ) (a : ComplexBox) (exponential cosine sine : Box) : ComplexBox :=
  let w := complexInverse S a
  let phase : ComplexBox := ⟨cosine,neg sine⟩
  complexAdd (complexTerms S w transformP)
    (realScale S (complexMul S (complexTerms S w transformQ) phase) exponential)

theorem transformEnclosure_contains (S : ℕ) (hS : 0 < S)
    (a : ComplexBox) (exponential cosine sine : Box) (r t : ℝ)
    (hz : ContainsComplex a ((r:ℂ)+(t:ℂ)*Complex.I))
    (hpositive : (0:ℝ) < (squaredNorm S a).lo)
    (he : Contains exponential (Real.exp (-2*r)))
    (hc : Contains cosine (Real.cos (2*t))) (hs : Contains sine (Real.sin (2*t))) :
    ContainsComplex (transformEnclosure S a exponential cosine sine)
      (goldbachMiddleG ((r:ℂ)+(t:ℂ)*Complex.I)) := by
  let z : ℂ := (r:ℂ)+(t:ℂ)*Complex.I
  have hw := complexInverse_contains S hS a z hz hpositive
  have hp := complexTerms_contains S hS (complexInverse S a) z⁻¹ hw transformP
  have hq := complexTerms_contains S hS (complexInverse S a) z⁻¹ hw transformQ
  dsimp [transformP, transformQ] at hp hq
  norm_num at hp hq
  let phase : ComplexBox := ⟨cosine, neg sine⟩
  have hphase : ContainsComplex phase
      ((Real.cos (2*t):ℂ)-(Real.sin (2*t):ℂ)*Complex.I) := by
    constructor
    · simpa only [phase, Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] using hc
    · simpa only [phase, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_sub] using
        neg_contains sine (Real.sin (2*t)) hs
  have h := complexAdd_contains _ _ _ _ hp
    (realScale_contains S hS _ exponential _ (Real.exp (-2*r))
      (complexMul_contains S hS _ phase _ _ hq hphase) he)
  convert h using 1
  · simp only [transformEnclosure, transformP, transformQ, phase, neg_div]
  · unfold goldbachMiddleG
    have hphaseExp : Complex.exp (-2*z) =
        ((Real.cos (2*t):ℂ)-(Real.sin (2*t):ℂ)*Complex.I)*(Real.exp (-2*r):ℂ) := by
      apply Complex.ext <;> simp only [z, Complex.exp_re, Complex.exp_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.re_ofNat, Complex.im_ofNat,
        Complex.neg_re, Complex.neg_im, zero_mul, mul_zero, mul_one, sub_zero, add_zero,
        zero_add, zero_sub, Real.cos_neg, Real.sin_neg, neg_mul]
        <;> ring
    rw [hphaseExp]
    dsimp [z]
    simp only [← inv_pow]
    ring


end GoldbachInterval

-- Dependency: Verification.Check_GoldbachIntegerComplexIntervals

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval.Integer

structure ComplexBox where
  re : Box
  im : Box

def liftComplex (S : ℕ) (a : ComplexBox) : GoldbachInterval.ComplexBox :=
  ⟨lift S a.re,lift S a.im⟩
def realPoint (S : ℕ) (q : ℚ) : ComplexBox := ⟨point S q,point S 0⟩
def complexAdd (a b : ComplexBox) : ComplexBox := ⟨add a.re b.re,add a.im b.im⟩
def complexNeg (a : ComplexBox) : ComplexBox := ⟨neg a.re,neg a.im⟩
def complexSub (a b : ComplexBox) : ComplexBox := complexAdd a (complexNeg b)
def complexMul (S : ℕ) (a b : ComplexBox) : ComplexBox :=
  ⟨sub (mul S a.re b.re) (mul S a.im b.im),
   add (mul S a.re b.im) (mul S a.im b.re)⟩
def complexPower (S : ℕ) (a : ComplexBox) : ℕ → ComplexBox
  | 0 => realPoint S 1
  | n+1 => complexMul S a (complexPower S a n)
def squaredNorm (S : ℕ) (a : ComplexBox) : Box := add (square S a.re) (square S a.im)
def complexInverse (S : ℕ) (a : ComplexBox) : ComplexBox :=
  ⟨divide S a.re (squaredNorm S a),divide S (neg a.im) (squaredNorm S a)⟩
def realScale (S : ℕ) (a : ComplexBox) (b : Box) : ComplexBox := ⟨mul S a.re b,mul S a.im b⟩

theorem lift_realPoint (S : ℕ) (q : ℚ) :
    liftComplex S (realPoint S q) = GoldbachInterval.realPoint S q := by
  simp only [liftComplex,realPoint,GoldbachInterval.realPoint,lift_point]

theorem lift_complexAdd (S : ℕ) (a b : ComplexBox) :
    liftComplex S (complexAdd a b) = GoldbachInterval.complexAdd (liftComplex S a) (liftComplex S b) := by
  simp only [liftComplex,complexAdd,GoldbachInterval.complexAdd,lift_add]

theorem lift_complexMul (S : ℕ) (hS : 0 < S) (a b : ComplexBox) :
    liftComplex S (complexMul S a b) = GoldbachInterval.complexMul S (liftComplex S a) (liftComplex S b) := by
  simp only [liftComplex,complexMul,GoldbachInterval.complexMul,lift_sub,lift_add,lift_mul S hS]

theorem lift_complexPower (S : ℕ) (hS : 0 < S) (a : ComplexBox) (n : ℕ) :
    liftComplex S (complexPower S a n) = GoldbachInterval.complexPower S (liftComplex S a) n := by
  induction n with
  | zero => exact lift_realPoint S 1
  | succ n ih =>
    change liftComplex S (complexMul S a (complexPower S a n)) =
      GoldbachInterval.complexMul S (liftComplex S a)
        (GoldbachInterval.complexPower S (liftComplex S a) n)
    rw [lift_complexMul S hS,ih]

theorem lift_squaredNorm (S : ℕ) (hS : 0 < S) (a : ComplexBox) :
    lift S (squaredNorm S a) = GoldbachInterval.squaredNorm S (liftComplex S a) := by
  simp only [squaredNorm,GoldbachInterval.squaredNorm,liftComplex,lift_add,lift_square S hS]

theorem lift_complexInverse (S : ℕ) (hS : 0 < S) (a : ComplexBox) :
    liftComplex S (complexInverse S a) = GoldbachInterval.complexInverse S (liftComplex S a) := by
  simp only [liftComplex,complexInverse,GoldbachInterval.complexInverse,lift_divide S hS,lift_neg]
  rw [lift_squaredNorm S hS]
  rfl

theorem lift_realScale (S : ℕ) (hS : 0 < S) (a : ComplexBox) (b : Box) :
    liftComplex S (realScale S a b) = GoldbachInterval.realScale S (liftComplex S a) (lift S b) := by
  simp only [liftComplex,realScale,GoldbachInterval.realScale,lift_mul S hS]


end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachMiddleTaylor

open scoped BigOperators
set_option autoImplicit false

noncomputable def goldbachCosTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1:ℝ)^k*x^(2*k)/((2*k).factorial:ℝ)

noncomputable def goldbachSinTaylor (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1:ℝ)^k*x^(2*k+1)/((2*k+1).factorial:ℝ)

theorem goldbach_complex_taylor_even_odd (n : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (2*n), ((x:ℂ)*Complex.I)^k/(k.factorial:ℂ)) =
      (goldbachCosTaylor n x:ℂ)+(goldbachSinTaylor n x:ℂ)*Complex.I := by
  have heven (k : ℕ) : ((x:ℂ)*Complex.I)^(2*k) =
      (((-1:ℝ)^k*x^(2*k):ℝ):ℂ) := by
    rw [mul_pow, pow_mul Complex.I, Complex.I_sq]
    push_cast
    ring
  have hodd (k : ℕ) : ((x:ℂ)*Complex.I)^(2*k+1) =
      (((-1:ℝ)^k*x^(2*k+1):ℝ):ℂ)*Complex.I := by
    rw [pow_succ, heven]
    push_cast
    ring
  induction n with
  | zero => simp [goldbachCosTaylor, goldbachSinTaylor]
  | succ n ih =>
    have hn : 2*(n+1) = (2*n+1)+1 := by omega
    rw [hn, Finset.sum_range_succ, Finset.sum_range_succ, ih, heven, hodd]
    simp only [goldbachCosTaylor, goldbachSinTaylor, Finset.sum_range_succ]
    push_cast
    ring

theorem goldbach_real_exp_taylor_error (n : ℕ) (x Q : ℝ)
    (hx : |x| ≤ Q) (hadmiss : Q/((n:ℝ)+1) ≤ (1/2:ℝ)) :
    |Real.exp x-∑ k ∈ Finset.range n, x^k/(k.factorial:ℝ)| ≤
      2*Q^n/(n.factorial:ℝ) := by
  have hn : 0 < (n:ℝ)+1 := by positivity
  have ha : ‖(x:ℂ)‖/(n.succ:ℝ) ≤ (1/2:ℝ) := by
    simpa using (div_le_div_of_nonneg_right hx hn.le).trans hadmiss
  have h := Complex.exp_bound' ha
  have he : ((Real.exp x-∑ k ∈ Finset.range n, x^k/(k.factorial:ℝ):ℝ):ℂ) =
      Complex.exp (x:ℂ)-∑ k ∈ Finset.range n, (x:ℂ)^k/(k.factorial:ℂ) := by
    push_cast
    rfl
  rw [← he] at h
  have hr : |Real.exp x-∑ k ∈ Finset.range n, x^k/(k.factorial:ℝ)| ≤
      |x|^n/(n.factorial:ℝ)*2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using h
  calc
    _ ≤ |x|^n/(n.factorial:ℝ)*2 := hr
    _ ≤ Q^n/(n.factorial:ℝ)*2 := by gcongr
    _ = _ := by ring

theorem goldbach_trig_taylor_error (n : ℕ) (x Q : ℝ)
    (hx : |x| ≤ Q) (hadmiss : Q/((2*n:ℕ)+1) ≤ (1/2:ℝ)) :
    |Real.cos x-goldbachCosTaylor n x| ≤ 2*Q^(2*n)/((2*n).factorial:ℝ) ∧
    |Real.sin x-goldbachSinTaylor n x| ≤ 2*Q^(2*n)/((2*n).factorial:ℝ) := by
  have hn : 0 < ((2*n:ℕ):ℝ)+1 := by positivity
  have ha : ‖(x:ℂ)*Complex.I‖/((2*n).succ:ℝ) ≤ (1/2:ℝ) := by
    simpa using (div_le_div_of_nonneg_right hx hn.le).trans hadmiss
  have hb := Complex.exp_bound' ha
  have hreal : (Complex.exp ((x:ℂ)*Complex.I)).re = Real.cos x := by
    simp [Complex.exp_re]
  have himag : (Complex.exp ((x:ℂ)*Complex.I)).im = Real.sin x := by
    simp [Complex.exp_im]
  rw [goldbach_complex_taylor_even_odd] at hb
  have hnorm : ‖Complex.exp ((x:ℂ)*Complex.I)-
      ((goldbachCosTaylor n x:ℂ)+(goldbachSinTaylor n x:ℂ)*Complex.I)‖ ≤
      2*Q^(2*n)/((2*n).factorial:ℝ) := by
    calc
      _ ≤ ‖(x:ℂ)*Complex.I‖^(2*n)/((2*n).factorial:ℝ)*2 := hb
      _ = |x|^(2*n)/((2*n).factorial:ℝ)*2 := by simp
      _ ≤ Q^(2*n)/((2*n).factorial:ℝ)*2 := by gcongr
      _ = _ := by ring
  constructor
  · have h := (Complex.abs_re_le_norm _).trans hnorm
    simpa [Complex.sub_re, hreal] using h
  · have h := (Complex.abs_im_le_norm _).trans hnorm
    simpa [Complex.sub_im, himag] using h

open scoped BigOperators
set_option autoImplicit false

namespace GoldbachInterval

def expPolynomial (S n : ℕ) (a : Box) : Box :=
  horner S ((List.range n).map (fun k => (1:ℚ)/(k.factorial:ℚ))) a

def expEnclosure (S n : ℕ) (Q : ℚ) (a : Box) : Box :=
  inflate S (expPolynomial S n a) (2*Q^n/(n.factorial:ℚ))

theorem expPolynomial_contains (S n : ℕ) (hS : 0 < S) (a : Box) (x : ℝ)
    (hx : Contains a x) : Contains (expPolynomial S n a)
      (∑ k ∈ Finset.range n, x^k/(k.factorial:ℝ)) := by
  have h := horner_generated_coefficients_contains S hS n
    (fun k => (1:ℚ)/(k.factorial:ℚ)) a x hx
  simpa only [expPolynomial, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul, Rat.cast_inv] using h

theorem expEnclosure_contains (S n : ℕ) (hS : 0 < S) (Q : ℚ) (a : Box) (x : ℝ)
    (hx : Contains a x) (hbound : |x| ≤ (Q:ℝ))
    (hadmiss : (Q:ℝ)/((n:ℝ)+1) ≤ (1/2:ℝ)) :
    Contains (expEnclosure S n Q a) (Real.exp x) := by
  apply inflate_contains S hS (expPolynomial S n a) _ _ _ (expPolynomial_contains S n hS a x hx)
  have h := goldbach_real_exp_taylor_error n x Q hbound hadmiss
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_natCast] using h

def cosPolynomial (S n : ℕ) (a : Box) : Box :=
  horner S ((List.range n).map (fun k => (-1:ℚ)^k/((2*k).factorial:ℚ))) (square S a)

def sinPolynomial (S n : ℕ) (a : Box) : Box :=
  mul S a (horner S ((List.range n).map (fun k => (-1:ℚ)^k/((2*k+1).factorial:ℚ))) (square S a))

def cosEnclosure (S n : ℕ) (Q : ℚ) (a : Box) : Box :=
  inflate S (cosPolynomial S n a) (2*Q^(2*n)/((2*n).factorial:ℚ))

def sinEnclosure (S n : ℕ) (Q : ℚ) (a : Box) : Box :=
  inflate S (sinPolynomial S n a) (2*Q^(2*n)/((2*n).factorial:ℚ))

theorem cosPolynomial_contains (S n : ℕ) (hS : 0 < S) (a : Box) (x : ℝ)
    (hx : Contains a x) : Contains (cosPolynomial S n a) (goldbachCosTaylor n x) := by
  have h := horner_generated_coefficients_contains S hS n
    (fun k => (-1:ℚ)^k/((2*k).factorial:ℚ)) (square S a) (x^2) (square_contains S hS a x hx)
  convert h using 1
  unfold goldbachCosTaylor
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rw [← pow_mul]
  ring

theorem sinPolynomial_contains (S n : ℕ) (hS : 0 < S) (a : Box) (x : ℝ)
    (hx : Contains a x) : Contains (sinPolynomial S n a) (goldbachSinTaylor n x) := by
  have hp := horner_generated_coefficients_contains S hS n
    (fun k => (-1:ℚ)^k/((2*k+1).factorial:ℚ)) (square S a) (x^2) (square_contains S hS a x hx)
  have h := mul_contains S hS a _ x _ hx hp
  convert h using 1
  unfold goldbachSinTaylor
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  push_cast
  rw [← pow_mul, pow_succ]
  ring

theorem trigEnclosures_contains (S n : ℕ) (hS : 0 < S) (Q : ℚ) (a : Box) (x : ℝ)
    (hx : Contains a x) (hbound : |x| ≤ (Q:ℝ))
    (hadmiss : (Q:ℝ)/((2*n:ℕ)+1) ≤ (1/2:ℝ)) :
    Contains (cosEnclosure S n Q a) (Real.cos x) ∧
      Contains (sinEnclosure S n Q a) (Real.sin x) := by
  have h := goldbach_trig_taylor_error n x Q hbound hadmiss
  constructor
  · apply inflate_contains S hS (cosPolynomial S n a) _ _ _ (cosPolynomial_contains S n hS a x hx)
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast] using h.1
  · apply inflate_contains S hS (sinPolynomial S n a) _ _ _ (sinPolynomial_contains S n hS a x hx)
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_natCast] using h.2


def cosMidpointEnclosure (S n : ℕ) (Q center radius : ℚ) : Box :=
  inflate S (cosEnclosure S n Q (point S center)) radius

def sinMidpointEnclosure (S n : ℕ) (Q center radius : ℚ) : Box :=
  inflate S (sinEnclosure S n Q (point S center)) radius

theorem trigMidpointEnclosures_contains (S n : ℕ) (hS : 0 < S)
    (Q center radius : ℚ) (x : ℝ)
    (hcenter : |(center:ℝ)| ≤ (Q:ℝ))
    (hadmiss : (Q:ℝ)/((2*n:ℕ)+1) ≤ (1/2:ℝ))
    (hradius : |x-(center:ℝ)| ≤ (radius:ℝ)) :
    Contains (cosMidpointEnclosure S n Q center radius) (Real.cos x) ∧
      Contains (sinMidpointEnclosure S n Q center radius) (Real.sin x) := by
  have hb := trigEnclosures_contains S n hS Q (point S center) center
    (point_contains S hS center) hcenter hadmiss
  constructor
  · exact inflate_contains S hS _ (Real.cos center) (Real.cos x) radius hb.1
      ((Real.abs_cos_sub_cos_le x center).trans hradius)
  · exact inflate_contains S hS _ (Real.sin center) (Real.sin x) radius hb.2
      ((Real.abs_sin_sub_sin_le x center).trans hradius)


end GoldbachInterval

-- Dependency: Verification.Check_GoldbachWeightedNormalizerTaylor


open MeasureTheory
open scoped BigOperators
set_option autoImplicit false

private noncomputable def Verification_Check_GoldbachWeightedNormalizerTaylor_private_kernel (u : ℝ) : ℝ := (2-u)^3*(4+6*u+u^2)/30

noncomputable def goldbachNormalizerMoment (j : ℕ) : ℝ :=
  4*(2:ℝ)^(j+4)/(5*((j:ℝ)+1)*((j:ℝ)+2)*((j:ℝ)+3)*((j:ℝ)+4)) +
  6*(2:ℝ)^(j+5)/(5*((j:ℝ)+2)*((j:ℝ)+3)*((j:ℝ)+4)*((j:ℝ)+5)) +
  (2:ℝ)^(j+6)/(5*((j:ℝ)+3)*((j:ℝ)+4)*((j:ℝ)+5)*((j:ℝ)+6))

open scoped BigOperators
set_option autoImplicit false

namespace GoldbachInterval

def momentRat (j : ℕ) : ℚ :=
  4*(2:ℚ)^(j+4)/(5*((j:ℚ)+1)*((j:ℚ)+2)*((j:ℚ)+3)*((j:ℚ)+4)) +
  6*(2:ℚ)^(j+5)/(5*((j:ℚ)+2)*((j:ℚ)+3)*((j:ℚ)+4)*((j:ℚ)+5)) +
  (2:ℚ)^(j+6)/(5*((j:ℚ)+3)*((j:ℚ)+4)*((j:ℚ)+5)*((j:ℚ)+6))

def normalizerPolynomial (S m n : ℕ) (a : Box) : Box :=
  horner S ((List.range n).map (fun k => momentRat (k+m)/(k.factorial:ℚ))) (neg a)

def normalizerEnclosure (S m n : ℕ) (error : ℚ) (a : Box) : Box :=
  inflate S (normalizerPolynomial S m n a) error

def endpointEnvelope (lower upper : Box) : Box := ⟨lower.lo, upper.hi⟩

theorem monotone_endpoint_envelope_contains (f : ℝ → ℝ) (hf : Monotone f)
    (a lower upper : Box) (r : ℝ) (hr : Contains a r)
    (hlower : Contains lower (f a.lo)) (hupper : Contains upper (f a.hi)) :
    Contains (endpointEnvelope lower upper) (f r) :=
  ⟨hlower.1.trans (hf hr.1), (hf hr.2).trans hupper.2⟩

end GoldbachInterval

-- Dependency: Verification.Check_GoldbachIntegerEnclosures

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval.Integer

def grid (n : ℤ) : Box := ⟨n,n⟩

theorem point_grid (S : ℕ) (hS : 0 < S) (n : ℤ) :
    point S ((n:ℚ)/(S:ℚ)) = grid n := by
  have hs : (S:ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hS)
  have h : (n:ℚ)/(S:ℚ)*(S:ℚ) = (n:ℚ) := div_mul_cancel₀ _ hs
  have hn : -((n:ℚ)/(S:ℚ))*(S:ℚ) = ((-n:ℤ):ℚ) := by
    rw [neg_mul,h,Int.cast_neg]
  simp only [point,grid,h,hn,Int.floor_intCast,neg_neg]

theorem lift_grid (S : ℕ) (hS : 0 < S) (n : ℤ) :
    lift S (grid n) = GoldbachInterval.point S ((n:ℚ)/(S:ℚ)) := by
  rw [← point_grid S hS n,lift_point]

def expPolynomial (S n : ℕ) (a : Box) : Box :=
  horner S ((List.range n).map (fun k => (1:ℚ)/(k.factorial:ℚ))) a

def expEnclosure (S n : ℕ) (Q : ℚ) (a : Box) : Box :=
  inflate S (expPolynomial S n a) (2*Q^n/(n.factorial:ℚ))

def cosPolynomial (S n : ℕ) (a : Box) : Box :=
  horner S ((List.range n).map (fun k => (-1:ℚ)^k/((2*k).factorial:ℚ))) (square S a)

def sinPolynomial (S n : ℕ) (a : Box) : Box :=
  mul S a (horner S ((List.range n).map (fun k => (-1:ℚ)^k/((2*k+1).factorial:ℚ))) (square S a))

def cosEnclosure (S n : ℕ) (Q : ℚ) (a : Box) : Box :=
  inflate S (cosPolynomial S n a) (2*Q^(2*n)/((2*n).factorial:ℚ))

def sinEnclosure (S n : ℕ) (Q : ℚ) (a : Box) : Box :=
  inflate S (sinPolynomial S n a) (2*Q^(2*n)/((2*n).factorial:ℚ))

theorem lift_expPolynomial (S n : ℕ) (hS : 0 < S) (a : Box) :
    lift S (expPolynomial S n a) = GoldbachInterval.expPolynomial S n (lift S a) := by
  exact lift_horner S hS _ a

theorem lift_expEnclosure (S n : ℕ) (hS : 0 < S) (Q : ℚ) (a : Box) :
    lift S (expEnclosure S n Q a) = GoldbachInterval.expEnclosure S n Q (lift S a) := by
  simp only [expEnclosure,GoldbachInterval.expEnclosure,lift_inflate,lift_expPolynomial S n hS]

theorem lift_cosPolynomial (S n : ℕ) (hS : 0 < S) (a : Box) :
    lift S (cosPolynomial S n a) = GoldbachInterval.cosPolynomial S n (lift S a) := by
  simp only [cosPolynomial,GoldbachInterval.cosPolynomial,lift_horner S hS,lift_square S hS]

theorem lift_sinPolynomial (S n : ℕ) (hS : 0 < S) (a : Box) :
    lift S (sinPolynomial S n a) = GoldbachInterval.sinPolynomial S n (lift S a) := by
  simp only [sinPolynomial,GoldbachInterval.sinPolynomial,lift_mul S hS,lift_horner S hS,lift_square S hS]

theorem lift_cosEnclosure (S n : ℕ) (hS : 0 < S) (Q : ℚ) (a : Box) :
    lift S (cosEnclosure S n Q a) = GoldbachInterval.cosEnclosure S n Q (lift S a) := by
  simp only [cosEnclosure,GoldbachInterval.cosEnclosure,lift_inflate,lift_cosPolynomial S n hS]

theorem lift_sinEnclosure (S n : ℕ) (hS : 0 < S) (Q : ℚ) (a : Box) :
    lift S (sinEnclosure S n Q a) = GoldbachInterval.sinEnclosure S n Q (lift S a) := by
  simp only [sinEnclosure,GoldbachInterval.sinEnclosure,lift_inflate,lift_sinPolynomial S n hS]

def normalizerPolynomial (S m n : ℕ) (a : Box) : Box :=
  horner S ((List.range n).map (fun k => momentRat (k+m)/(k.factorial:ℚ))) (neg a)

def normalizerEnclosure (S m n : ℕ) (error : ℚ) (a : Box) : Box :=
  inflate S (normalizerPolynomial S m n a) error

end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachDerivativeEnclosures

set_option autoImplicit false

namespace GoldbachInterval

noncomputable def termsValue (z : ℂ) (terms : List (ℚ×ℕ)) : ℂ :=
  terms.foldl (fun (acc : ℂ) (term : ℚ×ℕ) => acc+z^term.2*((term.1:ℝ):ℂ)) 0

def polynomialTransform (S : ℕ) (a : ComplexBox) (exponential cosine sine : Box)
    (P Q : List (ℚ×ℕ)) : ComplexBox :=
  let w := complexInverse S a
  let phase : ComplexBox := ⟨cosine,neg sine⟩
  complexAdd (complexTerms S w P)
    (realScale S (complexMul S (complexTerms S w Q) phase) exponential)

def derivativeP : List (ℚ×ℕ) := [(-16/15,2),(8,4),(-16,5),(24,7)]
def derivativeQ : List (ℚ×ℕ) := [(-8,4),(-32,5),(-48,6),(-24,7)]
def secondDerivativeP : List (ℚ×ℕ) := [(32/15,3),(-32,5),(80,6),(-168,8)]
def secondDerivativeQ : List (ℚ×ℕ) := [(16,4),(96,5),(256,6),(336,7),(168,8)]

end GoldbachInterval

-- Dependency: Verification.Check_GoldbachIntegerTransformEnclosures

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval.Integer

def enlarge (a : Box) (radius : ℤ) : Box := ⟨a.lo-radius,a.hi+radius⟩

theorem lift_enlarge (S : ℕ) (hS : 0 < S) (a : Box) (radius : ℤ) :
    lift S (enlarge a radius) = GoldbachInterval.inflate S (lift S a) ((radius:ℚ)/(S:ℚ)) := by
  have h : GoldbachInterval.up S ((radius:ℚ)/(S:ℚ)) = (radius:ℚ)/(S:ℚ) :=
    (congrArg GoldbachInterval.Box.hi (lift_grid S hS radius)).symm
  simp only [lift,enlarge,GoldbachInterval.inflate,Int.cast_sub,Int.cast_add,sub_div,add_div,h]

def cosMidpointEnclosure (S n : ℕ) (Q : ℚ) (center radius : ℤ) : Box :=
  enlarge (cosEnclosure S n Q (grid center)) radius

def sinMidpointEnclosure (S n : ℕ) (Q : ℚ) (center radius : ℤ) : Box :=
  enlarge (sinEnclosure S n Q (grid center)) radius

theorem lift_cosMidpointEnclosure (S n : ℕ) (hS : 0 < S) (Q : ℚ) (center radius : ℤ) :
    lift S (cosMidpointEnclosure S n Q center radius) =
      GoldbachInterval.cosMidpointEnclosure S n Q ((center:ℚ)/(S:ℚ)) ((radius:ℚ)/(S:ℚ)) := by
  simp only [cosMidpointEnclosure,GoldbachInterval.cosMidpointEnclosure,lift_enlarge S hS,
    lift_cosEnclosure S n hS,lift_grid S hS]

theorem lift_sinMidpointEnclosure (S n : ℕ) (hS : 0 < S) (Q : ℚ) (center radius : ℤ) :
    lift S (sinMidpointEnclosure S n Q center radius) =
      GoldbachInterval.sinMidpointEnclosure S n Q ((center:ℚ)/(S:ℚ)) ((radius:ℚ)/(S:ℚ)) := by
  simp only [sinMidpointEnclosure,GoldbachInterval.sinMidpointEnclosure,lift_enlarge S hS,
    lift_sinEnclosure S n hS,lift_grid S hS]

def complexTerm (S : ℕ) (a : ComplexBox) (term : ℚ×ℕ) : ComplexBox :=
  complexMul S (complexPower S a term.2) (realPoint S term.1)
def complexTerms (S : ℕ) (a : ComplexBox) (terms : List (ℚ×ℕ)) : ComplexBox :=
  terms.foldl (fun acc term => complexAdd acc (complexTerm S a term)) (realPoint S 0)

theorem lift_complexTerm (S : ℕ) (hS : 0 < S) (a : ComplexBox) (term : ℚ×ℕ) :
    liftComplex S (complexTerm S a term) = GoldbachInterval.complexTerm S (liftComplex S a) term := by
  simp only [complexTerm,GoldbachInterval.complexTerm,lift_complexMul S hS,
    lift_complexPower S hS,lift_realPoint]

private theorem Verification_Check_GoldbachIntegerTransformEnclosures_private_lift_termsFold (S : ℕ) (hS : 0 < S) (a : ComplexBox)
    (terms : List (ℚ×ℕ)) (initial : ComplexBox) :
    liftComplex S (terms.foldl (fun acc term => complexAdd acc (complexTerm S a term)) initial) =
    terms.foldl (fun acc term => GoldbachInterval.complexAdd acc
      (GoldbachInterval.complexTerm S (liftComplex S a) term)) (liftComplex S initial) := by
  induction terms generalizing initial with
  | nil => rfl
  | cons term terms ih =>
    simp only [List.foldl_cons]
    rw [ih,lift_complexAdd,lift_complexTerm S hS]

theorem lift_complexTerms (S : ℕ) (hS : 0 < S) (a : ComplexBox) (terms : List (ℚ×ℕ)) :
    liftComplex S (complexTerms S a terms) = GoldbachInterval.complexTerms S (liftComplex S a) terms := by
  unfold complexTerms GoldbachInterval.complexTerms
  rw [Verification_Check_GoldbachIntegerTransformEnclosures_private_lift_termsFold S hS,lift_realPoint]

def polynomialTransform (S : ℕ) (a : ComplexBox) (exponential cosine sine : Box)
    (P Q : List (ℚ×ℕ)) : ComplexBox :=
  let w := complexInverse S a
  let phase : ComplexBox := ⟨cosine,neg sine⟩
  complexAdd (complexTerms S w P)
    (realScale S (complexMul S (complexTerms S w Q) phase) exponential)

theorem lift_polynomialTransform (S : ℕ) (hS : 0 < S) (a : ComplexBox)
    (exponential cosine sine : Box) (P Q : List (ℚ×ℕ)) :
    liftComplex S (polynomialTransform S a exponential cosine sine P Q) =
    GoldbachInterval.polynomialTransform S (liftComplex S a) (lift S exponential)
      (lift S cosine) (lift S sine) P Q := by
  simp only [polynomialTransform,GoldbachInterval.polynomialTransform,lift_complexAdd,
    lift_complexTerms S hS,lift_realScale S hS,lift_complexMul S hS,lift_complexInverse S hS]
  simp only [liftComplex,lift_neg]

def transformEnclosure (S : ℕ) (a : ComplexBox) (exponential cosine sine : Box) : ComplexBox :=
  polynomialTransform S a exponential cosine sine transformP transformQ

theorem lift_transformEnclosure (S : ℕ) (hS : 0 < S) (a : ComplexBox)
    (exponential cosine sine : Box) :
    liftComplex S (transformEnclosure S a exponential cosine sine) =
    GoldbachInterval.transformEnclosure S (liftComplex S a) (lift S exponential)
      (lift S cosine) (lift S sine) := by
  rw [transformEnclosure,lift_polynomialTransform S hS]
  rfl


end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachRectangleCover

set_option autoImplicit false

namespace GoldbachInterval

structure Rectangle where
  rlo : ℚ
  rhi : ℚ
  tlo : ℚ
  thi : ℚ

def InRectangle (b : Rectangle) (r t : ℝ) : Prop :=
  (b.rlo:ℝ) ≤ r ∧ r ≤ b.rhi ∧ (b.tlo:ℝ) ≤ t ∧ t ≤ b.thi

inductive CoverTree where
  | leaf
  | splitR (middle : ℚ) (left right : CoverTree)
  | splitT (middle : ℚ) (left right : CoverTree)

def coverCheck (leafCheck : Rectangle → Bool) (b : Rectangle) : CoverTree → Bool
  | .leaf => leafCheck b
  | .splitR m left right =>
    coverCheck leafCheck {b with rhi := m} left && coverCheck leafCheck {b with rlo := m} right
  | .splitT m left right =>
    coverCheck leafCheck {b with thi := m} left && coverCheck leafCheck {b with tlo := m} right

-- Midpoints need not be interior: even an extended child must prove its whole box.
-- Thus a successful checker cannot hide a coverage hole behind invalid cuts.
end GoldbachInterval

-- Dependency: Verification.Check_GoldbachNegativeCertificateChecker

set_option autoImplicit false

namespace GoldbachInterval

def negativeZBox (b : Rectangle) : ComplexBox := ⟨neg ⟨b.rlo,b.rhi⟩,⟨b.tlo,b.thi⟩⟩
def negativeExpLower (S : ℕ) (b : Rectangle) : Box :=
  expEnclosure S 48 3 (point S (2*b.rlo))
def negativeExpUpper (S : ℕ) (b : Rectangle) : Box :=
  expEnclosure S 48 3 (point S (2*b.rhi))
def negativeExpBox (S : ℕ) (b : Rectangle) : Box :=
  endpointEnvelope (negativeExpLower S b) (negativeExpUpper S b)
def negativeCosBox (S : ℕ) (b : Rectangle) : Box :=
  cosMidpointEnclosure S 64 16 (b.tlo+b.thi) (b.thi-b.tlo)
def negativeSinBox (S : ℕ) (b : Rectangle) : Box :=
  sinMidpointEnclosure S 64 16 (b.tlo+b.thi) (b.thi-b.tlo)
def negativeTransformBox (S : ℕ) (b : Rectangle) : ComplexBox :=
  transformEnclosure S (negativeZBox b) (negativeExpBox S b)
    (negativeCosBox S b) (negativeSinBox S b)

def negativeLeafCheck (S : ℕ) (b : Rectangle) : Bool :=
  decide (|2*b.rlo| ≤ 3 ∧ |2*b.rhi| ≤ 3 ∧ |b.tlo+b.thi| ≤ 16 ∧
    0 < (squaredNorm S (negativeZBox b)).lo ∧ (negativeTransformBox S b).re.hi ≤ 0)

theorem negativeLeafCheck_sound (S : ℕ) (hS : 0 < S) (box : Rectangle)
    (hcheck : negativeLeafCheck S box = true) (b t : ℝ) (hbt : InRectangle box b t) :
    (goldbachMiddleG (((-b:ℝ):ℂ)+(t:ℂ)*Complex.I)).re ≤ 0 := by
  have conditions : |2*box.rlo| ≤ 3 ∧ |2*box.rhi| ≤ 3 ∧ |box.tlo+box.thi| ≤ 16 ∧
      0 < (squaredNorm S (negativeZBox box)).lo ∧ (negativeTransformBox S box).re.hi ≤ 0 :=
    of_decide_eq_true hcheck
  rcases conditions with ⟨hlo,hhi,hcenter,hden,hsign⟩
  have hb : Contains (⟨box.rlo,box.rhi⟩ : Box) b := ⟨hbt.1,hbt.2.1⟩
  have ht : Contains (⟨box.tlo,box.thi⟩ : Box) t := ⟨hbt.2.2.1,hbt.2.2.2⟩
  have harg : Contains (⟨2*box.rlo,2*box.rhi⟩ : Box) (2*b) := by
    constructor <;> dsimp <;> push_cast <;> linarith [hb.1,hb.2]
  have hlo' : |((2*box.rlo:ℚ):ℝ)| ≤ (3:ℝ) := by exact_mod_cast hlo
  have hhi' : |((2*box.rhi:ℚ):ℝ)| ≤ (3:ℝ) := by exact_mod_cast hhi
  have hlower := expEnclosure_contains S 48 hS 3 (point S (2*box.rlo))
    ((2*box.rlo:ℚ):ℝ) (point_contains S hS _) hlo' (by norm_num)
  have hupper := expEnclosure_contains S 48 hS 3 (point S (2*box.rhi))
    ((2*box.rhi:ℚ):ℝ) (point_contains S hS _) hhi' (by norm_num)
  have hexp := monotone_endpoint_envelope_contains Real.exp
    (fun _ _ h => Real.exp_le_exp.mpr h) (⟨2*box.rlo,2*box.rhi⟩ : Box)
    (negativeExpLower S box) (negativeExpUpper S box) (2*b) harg hlower hupper
  have hcenter' : |((box.tlo+box.thi:ℚ):ℝ)| ≤ (16:ℝ) := by exact_mod_cast hcenter
  have hradius : |2*t-((box.tlo+box.thi:ℚ):ℝ)| ≤ ((box.thi-box.tlo:ℚ):ℝ) := by
    push_cast
    apply abs_le.mpr
    constructor <;> linarith [ht.1,ht.2]
  have htrig := trigMidpointEnclosures_contains S 64 hS 16 (box.tlo+box.thi)
    (box.thi-box.tlo) (2*t) hcenter' (by norm_num) hradius
  have hz : ContainsComplex (negativeZBox box) (((-b:ℝ):ℂ)+(t:ℂ)*Complex.I) := by
    constructor
    · simpa only [negativeZBox, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        using neg_contains (⟨box.rlo,box.rhi⟩ : Box) b hb
    · simpa only [negativeZBox, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add] using ht
  have hden' : (0:ℝ) < (squaredNorm S (negativeZBox box)).lo := by exact_mod_cast hden
  have h := transformEnclosure_contains S hS (negativeZBox box)
    (negativeExpBox S box) (negativeCosBox S box) (negativeSinBox S box) (-b) t
    hz hden' (by simpa only [negativeExpBox, neg_mul, mul_neg, neg_neg] using hexp) htrig.1 htrig.2
  exact h.1.2.trans (by exact_mod_cast hsign)

end GoldbachInterval

-- Dependency: Verification.Check_GoldbachTransformRectangleEnclosures

set_option autoImplicit false

namespace GoldbachInterval

def rectangleZBox (b : Rectangle) : ComplexBox := ⟨⟨b.rlo,b.rhi⟩,⟨b.tlo,b.thi⟩⟩
def rectangleExpBox (S : ℕ) (b : Rectangle) : Box :=
  endpointEnvelope
    (expEnclosure S 48 3 (point S (-2*b.rhi)))
    (expEnclosure S 48 3 (point S (-2*b.rlo)))
def rectangleTransformBox (S : ℕ) (b : Rectangle) : ComplexBox :=
  transformEnclosure S (rectangleZBox b) (rectangleExpBox S b)
    (negativeCosBox S b) (negativeSinBox S b)
def rectangleDerivativeBox (S : ℕ) (b : Rectangle) : ComplexBox :=
  polynomialTransform S (rectangleZBox b) (rectangleExpBox S b)
    (negativeCosBox S b) (negativeSinBox S b) derivativeP derivativeQ
def rectangleSecondDerivativeBox (S : ℕ) (b : Rectangle) : ComplexBox :=
  polynomialTransform S (rectangleZBox b) (rectangleExpBox S b)
    (negativeCosBox S b) (negativeSinBox S b) secondDerivativeP secondDerivativeQ

end GoldbachInterval

-- Dependency: Verification.Check_GoldbachMonotonicityEnclosures

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval

def normalizerBudget (m : ℕ) : ℚ :=
  (if m = 0 then 16/9 else if m = 1 then 4 else 8)*(5/2)^48/((48:ℕ).factorial:ℚ)

def weightedNormalizerBox (S m : ℕ) (a : Box) : Box :=
  endpointEnvelope
    (normalizerEnclosure S m 48 (normalizerBudget m) (point S a.hi))
    (normalizerEnclosure S m 48 (normalizerBudget m) (point S a.lo))

def numeratorBox (S : ℕ) (z z1 : Box) (g g1 : ComplexBox) : Box :=
  add (mul S z g1.re) (mul S z1 g.re)

def shiftGradientBox (S : ℕ) (z z2 : Box) (g g2 : ComplexBox) : Box :=
  sub (mul S z g2.re) (mul S z2 g.re)

def frequencyGradientBox (S : ℕ) (z z1 : Box) (g1 g2 : ComplexBox) : Box :=
  sub (mul S (neg z) g2.im) (mul S z1 g1.im)

end GoldbachInterval

-- Dependency: Verification.Check_GoldbachComplexTailEight

open MeasureTheory
set_option autoImplicit false

open MeasureTheory
set_option autoImplicit false

private noncomputable def Verification_Check_GoldbachKernelOrder_private_kernel (u : ℝ) : ℝ := (2-u)^3*(4+6*u+u^2)/30
private noncomputable def Verification_Check_GoldbachKernelOrder_private_G (z : ℝ) : ℝ := ∫ u in (0:ℝ)..2, Verification_Check_GoldbachKernelOrder_private_kernel u*Real.exp (-z*u)

private lemma Verification_Check_GoldbachKernelOrder_private_kernel_nonnegative (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 2) :
    0 ≤ Verification_Check_GoldbachKernelOrder_private_kernel u := by
  have hbase : 0 ≤ 2-u := by linarith [hu.2]
  have hpoly : 0 ≤ 4+6*u+u^2 := by nlinarith [hu.1,sq_nonneg u]
  unfold Verification_Check_GoldbachKernelOrder_private_kernel
  positivity

theorem laplace_positive (z : ℝ) : 0 < Verification_Check_GoldbachKernelOrder_private_G z := by
  unfold Verification_Check_GoldbachKernelOrder_private_G
  apply intervalIntegral.integral_pos (by norm_num)
  · have h : Continuous (fun u : ℝ => Verification_Check_GoldbachKernelOrder_private_kernel u*Real.exp (-z*u)) := by
      unfold Verification_Check_GoldbachKernelOrder_private_kernel
      fun_prop
    exact h.continuousOn
  · intro u hu
    exact mul_nonneg (Verification_Check_GoldbachKernelOrder_private_kernel_nonnegative u ⟨hu.1.le,hu.2⟩) (Real.exp_pos _).le
  · refine ⟨1,by norm_num,?_⟩
    have hk : 0 < Verification_Check_GoldbachKernelOrder_private_kernel 1 := by norm_num [Verification_Check_GoldbachKernelOrder_private_kernel]
    exact mul_pos hk (Real.exp_pos _)

private noncomputable def Verification_Check_GoldbachKernelOrder_private_psi (x lower position : ℝ) : ℝ :=
  Verification_Check_GoldbachKernelOrder_private_G ((position-lower)/x) / Verification_Check_GoldbachKernelOrder_private_G (-lower/x)

open scoped BigOperators

-- Distinct indices preserve multiplicity and prevent reusing one zero twice.
open MeasureTheory Set
set_option autoImplicit false

open MeasureTheory
set_option autoImplicit false

-- Local tail estimate; the bounded middle-frequency comparison remains separate.
theorem goldbach_polynomial_complex_real_part (r t : ℝ) :
    ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((r:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re =
    ∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-r*u)*Real.cos (t*u) := by
  have hf : IntervalIntegrable (fun u : ℝ => ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((r:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) volume (0:ℝ) 2 := by
    have hc : Continuous (fun u : ℝ => ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((r:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) := by fun_prop
    exact hc.intervalIntegrable (μ := volume) 0 2
  have hmap := Complex.reCLM.intervalIntegral_comp_comm hf
  calc
    _ = ∫ u in (0:ℝ)..2, Complex.reCLM (((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((r:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) := by exact hmap.symm
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro u _
      change (((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
        Complex.exp (-((r:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))).re = _
      simp only [Complex.mul_re, Complex.mul_im, Complex.exp_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
        zero_mul, mul_zero, mul_one, sub_zero, add_zero, zero_add,
        neg_mul, Real.cos_neg]
      ring

theorem goldbach_polynomial_real_part_even (r t : ℝ) :
    ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((r:ℂ)+((-t:ℝ):ℂ)*Complex.I)*(u:ℂ))) : ℂ).re =
    ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((r:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re := by
  rw [goldbach_polynomial_complex_real_part r (-t), goldbach_polynomial_complex_real_part r t]
  simp only [neg_mul, Real.cos_neg]


private noncomputable def Verification_Check_GoldbachComplexComparisonTail_private_goldbachNormalized (r t : ℝ) : ℝ :=
  ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
    Complex.exp (-((r:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
    (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-r*u))

-- The middle comparison is an explicit hypothesis, not a proved premise.
open MeasureTheory Set
set_option autoImplicit false

noncomputable def goldbachMiddleReal (r t : ℝ) : ℝ :=
  ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
    Complex.exp (-((r:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re

noncomputable def goldbachMiddleZ (r : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-r*u)

noncomputable def goldbachMiddlePhi (r t : ℝ) : ℝ :=
  goldbachMiddleReal r t / goldbachMiddleZ r

-- The derivative and sign premises remain explicit certificate obligations.
set_option autoImplicit false

namespace GoldbachInterval

def boxAbsBound (a : Box) : ℚ := max |a.lo| |a.hi|

def centeredSignCheck (center dr dt : Box) (radiusR radiusT : ℚ) : Bool :=
  decide (0 ≤ center.lo-boxAbsBound dr*radiusR-boxAbsBound dt*radiusT)

end GoldbachInterval

-- Dependency: Verification.Check_GoldbachMonotonicityCertificateChecker

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval

def rectangleNormalizerBox (S m : ℕ) (b : Rectangle) : Box :=
  weightedNormalizerBox S m ⟨b.rlo,b.rhi⟩
def rectangleNumeratorBox (S : ℕ) (b : Rectangle) : Box :=
  numeratorBox S (rectangleNormalizerBox S 0 b) (rectangleNormalizerBox S 1 b)
    (rectangleTransformBox S b) (rectangleDerivativeBox S b)
def rectangleShiftGradientBox (S : ℕ) (b : Rectangle) : Box :=
  shiftGradientBox S (rectangleNormalizerBox S 0 b) (rectangleNormalizerBox S 2 b)
    (rectangleTransformBox S b) (rectangleSecondDerivativeBox S b)
def rectangleFrequencyGradientBox (S : ℕ) (b : Rectangle) : Box :=
  frequencyGradientBox S (rectangleNormalizerBox S 0 b) (rectangleNormalizerBox S 1 b)
    (rectangleDerivativeBox S b) (rectangleSecondDerivativeBox S b)
noncomputable def shiftGradient (r t : ℝ) : ℝ :=
  goldbachWeightedZ 0 r*(goldbachMiddleG2 ((r:ℂ)+(t:ℂ)*Complex.I)).re-
    goldbachWeightedZ 2 r*(goldbachMiddleG ((r:ℂ)+(t:ℂ)*Complex.I)).re
noncomputable def frequencyGradient (r t : ℝ) : ℝ :=
  -goldbachWeightedZ 0 r*(goldbachMiddleG2 ((r:ℂ)+(t:ℂ)*Complex.I)).im-
    goldbachWeightedZ 1 r*(goldbachMiddleG1 ((r:ℂ)+(t:ℂ)*Complex.I)).im

def pointRectangle (r t : ℚ) : Rectangle := ⟨r,r,t,t⟩
def coordinateRadius (lo hi center : ℚ) : ℚ := max (center-lo) (hi-center)

def monotonicityLeafCheck (S : ℕ) (box : Rectangle) (r₀ t₀ : ℚ) : Bool :=
  decide (|box.rlo| ≤ 5/4 ∧ |box.rhi| ≤ 5/4 ∧ |box.tlo+box.thi| ≤ 16 ∧
    |r₀| ≤ 5/4 ∧ |2*t₀| ≤ 16 ∧ box.rlo ≤ r₀ ∧ r₀ ≤ box.rhi ∧
    box.tlo ≤ t₀ ∧ t₀ ≤ box.thi ∧ 0 < box.tlo ∧
    0 < (squaredNorm S (rectangleZBox box)).lo ∧
    0 < (squaredNorm S (rectangleZBox (pointRectangle r₀ t₀))).lo) &&
  centeredSignCheck (rectangleNumeratorBox S (pointRectangle r₀ t₀))
    (rectangleShiftGradientBox S box) (rectangleFrequencyGradientBox S box)
    (coordinateRadius box.rlo box.rhi r₀) (coordinateRadius box.tlo box.thi t₀)

end GoldbachInterval

-- Dependency: Verification.Check_GoldbachIntegerRectangleEnclosures

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval.Integer

structure Rectangle where
  rlo : ℤ
  rhi : ℤ
  tlo : ℤ
  thi : ℤ

def liftRectangle (S : ℕ) (b : Rectangle) : GoldbachInterval.Rectangle :=
  ⟨(b.rlo:ℚ)/(S:ℚ),(b.rhi:ℚ)/(S:ℚ),(b.tlo:ℚ)/(S:ℚ),(b.thi:ℚ)/(S:ℚ)⟩
def pointRectangle (r t : ℤ) : Rectangle := ⟨r,r,t,t⟩
def endpointEnvelope (lower upper : Box) : Box := ⟨lower.lo,upper.hi⟩

theorem lift_endpointEnvelope (S : ℕ) (lower upper : Box) :
    lift S (endpointEnvelope lower upper) =
      GoldbachInterval.endpointEnvelope (lift S lower) (lift S upper) := rfl

def rectangleZBox (b : Rectangle) : ComplexBox := ⟨⟨b.rlo,b.rhi⟩,⟨b.tlo,b.thi⟩⟩
def rectangleExpBox (S : ℕ) (b : Rectangle) : Box :=
  endpointEnvelope (expEnclosure S 48 3 (grid (-2*b.rhi)))
    (expEnclosure S 48 3 (grid (-2*b.rlo)))
def rectangleCosBox (S : ℕ) (b : Rectangle) : Box :=
  cosMidpointEnclosure S 64 16 (b.tlo+b.thi) (b.thi-b.tlo)
def rectangleSinBox (S : ℕ) (b : Rectangle) : Box :=
  sinMidpointEnclosure S 64 16 (b.tlo+b.thi) (b.thi-b.tlo)
def rectangleTransformBox (S : ℕ) (b : Rectangle) : ComplexBox :=
  transformEnclosure S (rectangleZBox b) (rectangleExpBox S b)
    (rectangleCosBox S b) (rectangleSinBox S b)
def rectangleDerivativeBox (S : ℕ) (b : Rectangle) : ComplexBox :=
  polynomialTransform S (rectangleZBox b) (rectangleExpBox S b)
    (rectangleCosBox S b) (rectangleSinBox S b) derivativeP derivativeQ
def rectangleSecondDerivativeBox (S : ℕ) (b : Rectangle) : ComplexBox :=
  polynomialTransform S (rectangleZBox b) (rectangleExpBox S b)
    (rectangleCosBox S b) (rectangleSinBox S b) secondDerivativeP secondDerivativeQ

theorem lift_rectangleCosBox (S : ℕ) (hS : 0 < S) (b : Rectangle) :
    lift S (rectangleCosBox S b) = GoldbachInterval.negativeCosBox S (liftRectangle S b) := by
  simp only [rectangleCosBox,GoldbachInterval.negativeCosBox,lift_cosMidpointEnclosure S 64 hS,
    liftRectangle,Int.cast_add,Int.cast_sub,add_div,sub_div]

theorem lift_rectangleSinBox (S : ℕ) (hS : 0 < S) (b : Rectangle) :
    lift S (rectangleSinBox S b) = GoldbachInterval.negativeSinBox S (liftRectangle S b) := by
  simp only [rectangleSinBox,GoldbachInterval.negativeSinBox,lift_sinMidpointEnclosure S 64 hS,
    liftRectangle,Int.cast_add,Int.cast_sub,add_div,sub_div]

def rectangleNormalizerBox (S m : ℕ) (b : Rectangle) : Box :=
  endpointEnvelope (normalizerEnclosure S m 48 (normalizerBudget m) (grid b.rhi))
    (normalizerEnclosure S m 48 (normalizerBudget m) (grid b.rlo))

end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachIntegerMonotonicityEvaluator

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval.Integer

def rectangleNumeratorBox (S : ℕ) (b : Rectangle) : Box :=
  add (mul S (rectangleNormalizerBox S 0 b) (rectangleDerivativeBox S b).re)
    (mul S (rectangleNormalizerBox S 1 b) (rectangleTransformBox S b).re)
def rectangleShiftGradientBox (S : ℕ) (b : Rectangle) : Box :=
  sub (mul S (rectangleNormalizerBox S 0 b) (rectangleSecondDerivativeBox S b).re)
    (mul S (rectangleNormalizerBox S 2 b) (rectangleTransformBox S b).re)
def rectangleFrequencyGradientBox (S : ℕ) (b : Rectangle) : Box :=
  sub (mul S (neg (rectangleNormalizerBox S 0 b)) (rectangleSecondDerivativeBox S b).im)
    (mul S (rectangleNormalizerBox S 1 b) (rectangleDerivativeBox S b).im)

def boxAbsBound (a : Box) : ℤ := max |a.lo| |a.hi|
def coordinateRadius (lo hi center : ℤ) : ℤ := max (center-lo) (hi-center)
def centeredSignCheck (S : ℕ) (center dr dt : Box) (radiusR radiusT : ℤ) : Bool :=
  decide (0 ≤ center.lo*(S:ℤ)-boxAbsBound dr*radiusR-boxAbsBound dt*radiusT)

end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachIntegerMonotonicityChecker
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace GoldbachInterval.Integer

def monotonicityAdmissible (S : ℕ) (b : Rectangle) (r t : ℤ) : Bool :=
  let box := liftRectangle S b
  let r₀ : ℚ := (r:ℚ)/(S:ℚ)
  let t₀ : ℚ := (t:ℚ)/(S:ℚ)
  decide (|box.rlo| ≤ 5/4 ∧ |box.rhi| ≤ 5/4 ∧ |box.tlo+box.thi| ≤ 16 ∧
    |r₀| ≤ 5/4 ∧ |2*t₀| ≤ 16 ∧ box.rlo ≤ r₀ ∧ r₀ ≤ box.rhi ∧
    box.tlo ≤ t₀ ∧ t₀ ≤ box.thi ∧ 0 < box.tlo ∧
    0 < (GoldbachInterval.squaredNorm S (GoldbachInterval.rectangleZBox box)).lo ∧
    0 < (GoldbachInterval.squaredNorm S (GoldbachInterval.rectangleZBox (GoldbachInterval.pointRectangle r₀ t₀))).lo)

def monotonicityLeafCheck (S : ℕ) (b : Rectangle) (r₀ t₀ : ℤ) : Bool :=
  monotonicityAdmissible S b r₀ t₀ &&
  centeredSignCheck S (rectangleNumeratorBox S (pointRectangle r₀ t₀))
    (rectangleShiftGradientBox S b) (rectangleFrequencyGradientBox S b)
    (coordinateRadius b.rlo b.rhi r₀) (coordinateRadius b.tlo b.thi t₀)

end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachCachedTaylorTables
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace GoldbachInterval.Integer.Cached
deriving instance DecidableEq for GoldbachInterval.Integer.Box
def scale : ℕ := 2^768

def hornerBoxes (S : ℕ) : List Box → Box → Box
  | [], _ => point S 0
  | c::cs, a => add c (mul S a (hornerBoxes S cs a))

theorem hornerBoxes_map (S : ℕ) (coefficients : List ℚ) (a : Box) :
    hornerBoxes S (coefficients.map (point S)) a = horner S coefficients a := by
  induction coefficients with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, hornerBoxes, horner, ih]

def expTable : List Box := [
  ⟨1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856,1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856⟩,
  ⟨1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856,1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856⟩,
  ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928⟩,
  ⟨258753015383451489191496581410417092542814336186116101856508673004341825447729481055146401471441079658414621782855178867695263340685802398574047879173530189867409162670141650925044214271933074137543833198952744791815474475636009642,258753015383451489191496581410417092542814336186116101856508673004341825447729481055146401471441079658414621782855178867695263340685802398574047879173530189867409162670141650925044214271933074137543833198952744791815474475636009643⟩,
  ⟨64688253845862872297874145352604273135703584046529025464127168251085456361932370263786600367860269914603655445713794716923815835171450599643511969793382547466852290667535412731261053567983268534385958299738186197953868618909002410,64688253845862872297874145352604273135703584046529025464127168251085456361932370263786600367860269914603655445713794716923815835171450599643511969793382547466852290667535412731261053567983268534385958299738186197953868618909002411⟩,
  ⟨12937650769172574459574829070520854627140716809305805092825433650217091272386474052757320073572053982920731089142758943384763167034290119928702393958676509493370458133507082546252210713596653706877191659947637239590773723781800482,12937650769172574459574829070520854627140716809305805092825433650217091272386474052757320073572053982920731089142758943384763167034290119928702393958676509493370458133507082546252210713596653706877191659947637239590773723781800483⟩,
  ⟨2156275128195429076595804845086809104523452801550967515470905608369515212064412342126220012262008997153455181523793157230793861172381686654783732326446084915561743022251180424375368452266108951146198609991272873265128953963633413,2156275128195429076595804845086809104523452801550967515470905608369515212064412342126220012262008997153455181523793157230793861172381686654783732326446084915561743022251180424375368452266108951146198609991272873265128953963633414⟩,
  ⟨308039304027918439513686406440972729217636114507281073638700801195645030294916048875174287466001285307636454503399022461541980167483098093540533189492297845080249003178740060625052636038015564449456944284467553323589850566233344,308039304027918439513686406440972729217636114507281073638700801195645030294916048875174287466001285307636454503399022461541980167483098093540533189492297845080249003178740060625052636038015564449456944284467553323589850566233345⟩,
  ⟨38504913003489804939210800805121591152204514313410134204837600149455628786864506109396785933250160663454556812924877807692747520935387261692566648686537230635031125397342507578131579504751945556182118035558444165448731320779168,38504913003489804939210800805121591152204514313410134204837600149455628786864506109396785933250160663454556812924877807692747520935387261692566648686537230635031125397342507578131579504751945556182118035558444165448731320779169⟩,
  ⟨4278323667054422771023422311680176794689390479267792689426400016606180976318278456599642881472240073717172979213875311965860835659487473521396294298504136737225680599704723064236842167194660617353568670617604907272081257864352,4278323667054422771023422311680176794689390479267792689426400016606180976318278456599642881472240073717172979213875311965860835659487473521396294298504136737225680599704723064236842167194660617353568670617604907272081257864353⟩,
  ⟨427832366705442277102342231168017679468939047926779268942640001660618097631827845659964288147224007371717297921387531196586083565948747352139629429850413673722568059970472306423684216719466061735356867061760490727208125786435,427832366705442277102342231168017679468939047926779268942640001660618097631827845659964288147224007371717297921387531196586083565948747352139629429850413673722568059970472306423684216719466061735356867061760490727208125786436⟩,
  ⟨38893851518676570645667475560728879951721731629707206267512727423692554330166167787269480740656727942883390720126139199689643960540795213830875402713673970338415278179133846038516746974496914703214260641978226429746193253312,38893851518676570645667475560728879951721731629707206267512727423692554330166167787269480740656727942883390720126139199689643960540795213830875402713673970338415278179133846038516746974496914703214260641978226429746193253313⟩,
  ⟨3241154293223047553805622963394073329310144302475600522292727285307712860847180648939123395054727328573615893343844933307470330045066267819239616892806164194867939848261153836543062247874742891934521720164852202478849437776,3241154293223047553805622963394073329310144302475600522292727285307712860847180648939123395054727328573615893343844933307470330045066267819239616892806164194867939848261153836543062247874742891934521720164852202478849437777⟩,
  ⟨249319561017157504138894074107236409946934177113507732484055945023670220065167742226086415004209794505662761026449610254420794618851251370710739760985089553451379988327781064349466326759595607071886286166527092498373033675,249319561017157504138894074107236409946934177113507732484055945023670220065167742226086415004209794505662761026449610254420794618851251370710739760985089553451379988327781064349466326759595607071886286166527092498373033676⟩,
  ⟨17808540072654107438492433864802600710495298365250552320289710358833587147511981587577601071729271036118768644746400732458628187060803669336481411498934968103669999166270076024961880482828257647991877583323363749883788119,17808540072654107438492433864802600710495298365250552320289710358833587147511981587577601071729271036118768644746400732458628187060803669336481411498934968103669999166270076024961880482828257647991877583323363749883788120⟩,
  ⟨1187236004843607162566162257653506714033019891016703488019314023922239143167465439171840071448618069074584576316426715497241879137386911289098760766595664540244666611084671734997458698855217176532791838888224249992252541,1187236004843607162566162257653506714033019891016703488019314023922239143167465439171840071448618069074584576316426715497241879137386911289098760766595664540244666611084671734997458698855217176532791838888224249992252542⟩,
  ⟨74202250302725447660385141103344169627063743188543968001207126495139946447966589948240004465538629317161536019776669718577617446086681955568672547912229033765291663192791983437341168678451073533299489930514015624515783,74202250302725447660385141103344169627063743188543968001207126495139946447966589948240004465538629317161536019776669718577617446086681955568672547912229033765291663192791983437341168678451073533299489930514015624515784⟩,
  ⟨4364838253101496921199125947255539389827279011090821647129830970302349791056858232249412027384625253950678589398627630504565732122745997386392502818366413750899509599575999025725951098732416090194087642971412683795046,4364838253101496921199125947255539389827279011090821647129830970302349791056858232249412027384625253950678589398627630504565732122745997386392502818366413750899509599575999025725951098732416090194087642971412683795047⟩,
  ⟨242491014061194273399951441514196632768182167282823424840546165016797210614269901791634001521368069663926588299923757250253651784596999854799583489909245208383306088865333279206997283262912005010782646831745149099724,242491014061194273399951441514196632768182167282823424840546165016797210614269901791634001521368069663926588299923757250253651784596999854799583489909245208383306088865333279206997283262912005010782646831745149099725⟩,
  ⟨12762684950589172284207970606010349093062219330674917096870850790357747927066836936401789553756214192838241489469671434223876409715631571305241236311012905704384530992912277852999857013837473947935928780618165742090,12762684950589172284207970606010349093062219330674917096870850790357747927066836936401789553756214192838241489469671434223876409715631571305241236311012905704384530992912277852999857013837473947935928780618165742091⟩,
  ⟨638134247529458614210398530300517454653110966533745854843542539517887396353341846820089477687810709641912074473483571711193820485781578565262061815550645285219226549645613892649992850691873697396796439030908287104,638134247529458614210398530300517454653110966533745854843542539517887396353341846820089477687810709641912074473483571711193820485781578565262061815550645285219226549645613892649992850691873697396796439030908287105⟩,
  ⟨30387345120450410200495168109548450221576712692083135944930597119899399826349611753337594175610033792472003546356360557675896213608646598345812467407173585010439359506933994888094897651993985590323639953852775576,30387345120450410200495168109548450221576712692083135944930597119899399826349611753337594175610033792472003546356360557675896213608646598345812467407173585010439359506933994888094897651993985590323639953852775577⟩,
  ⟨1381242960020473190931598550434020464617123304185597088405936232722699992106800534242617917073183354203272888470743661712540736982211209015718748518507890227747243613951545222186131711454272072287438179720580708,1381242960020473190931598550434020464617123304185597088405936232722699992106800534242617917073183354203272888470743661712540736982211209015718748518507890227747243613951545222186131711454272072287438179720580709⟩,
  ⟨60054041740020573518765154366696541939874926268939003843736357944465217048121762358374692046660145834924908194380159204893075520965704739813858631239473488162923635389197618355918770063229220534236442596546987,60054041740020573518765154366696541939874926268939003843736357944465217048121762358374692046660145834924908194380159204893075520965704739813858631239473488162923635389197618355918770063229220534236442596546988⟩,
  ⟨2502251739167523896615214765279022580828121927872458493489014914352717377005073431598945501944172743121871174765839966870544813373571030825577442968311395340121818141216567431496615419301217522259851774856124,2502251739167523896615214765279022580828121927872458493489014914352717377005073431598945501944172743121871174765839966870544813373571030825577442968311395340121818141216567431496615419301217522259851774856125⟩,
  ⟨100090069566700955864608590611160903233124877114898339739560596574108695080202937263957820077766909724874846990633598674821792534942841233023097718732455813604872725648662697259864616772048700890394070994244,100090069566700955864608590611160903233124877114898339739560596574108695080202937263957820077766909724874846990633598674821792534942841233023097718732455813604872725648662697259864616772048700890394070994245⟩,
  ⟨3849618060257729071715715023506188585889418350573013066906176791311872887700112971690685387606419604802878730408984564416222789805493893577811450720479069754033566371102411433071716029694180803476695038240,3849618060257729071715715023506188585889418350573013066906176791311872887700112971690685387606419604802878730408984564416222789805493893577811450720479069754033566371102411433071716029694180803476695038241⟩,
  ⟨142578446676212187841322778648377355032941420391593076552080621900439736581485665618173532874311837214921434459592020904304547770573847910289312989647372953853095050781570793817470964062747437165803519934,142578446676212187841322778648377355032941420391593076552080621900439736581485665618173532874311837214921434459592020904304547770573847910289312989647372953853095050781570793817470964062747437165803519935⟩,
  ⟨5092087381293292422904384951727762679747907871128324162574307925015704877910202343506197602653994186247194087842572175153733848949065996796046892487406176923324823242198956922052534430812408470207268569,5092087381293292422904384951727762679747907871128324162574307925015704877910202343506197602653994186247194087842572175153733848949065996796046892487406176923324823242198956922052534430812408470207268570⟩,
  ⟨175589220044596290444978791438888368267169236935459453881872687069507064755524218741593020781172213318868761649743868108749443067209172303311961809910557824942235284213757135243190842441807188627836847,175589220044596290444978791438888368267169236935459453881872687069507064755524218741593020781172213318868761649743868108749443067209172303311961809910557824942235284213757135243190842441807188627836848⟩,
  ⟨5852974001486543014832626381296278942238974564515315129395756235650235491850807291386434026039073777295625388324795603624981435573639076777065393663685260831407842807125237841439694748060239620927894,5852974001486543014832626381296278942238974564515315129395756235650235491850807291386434026039073777295625388324795603624981435573639076777065393663685260831407842807125237841439694748060239620927895⟩,
  ⟨188805612951178806930084721977299320717386276274687584819217943085491467479058299722143033098034637977278238333057922697580046308827066992808561085925330994561543316358878640046441766066459342610577,188805612951178806930084721977299320717386276274687584819217943085491467479058299722143033098034637977278238333057922697580046308827066992808561085925330994561543316358878640046441766066459342610578⟩,
  ⟨5900175404724337716565147561790603772418321133583987025600560721421608358720571866316969784313582436789944947908060084299376447150845843525267533935166593580048228636214957501451305189576854456580,5900175404724337716565147561790603772418321133583987025600560721421608358720571866316969784313582436789944947908060084299376447150845843525267533935166593580048228636214957501451305189576854456581⟩,
  ⟨178793194082555688380762047326987993103585488896484455321229112770351768446077935342938478312532801114846816603274548009072013550025631621977804058641411926668128140491362348528827429987177407775,178793194082555688380762047326987993103585488896484455321229112770351768446077935342938478312532801114846816603274548009072013550025631621977804058641411926668128140491362348528827429987177407776⟩,
  ⟨5258623355369284952375354333146705679517220261661307509447915081480934366061115745380543479780376503377847547155133764972706280883106812411111884077688586078474357073275363192024336176093453169,5258623355369284952375354333146705679517220261661307509447915081480934366061115745380543479780376503377847547155133764972706280883106812411111884077688586078474357073275363192024336176093453170⟩,
  ⟨150246381581979570067867266661334447986206293190323071698511859470883839030317592725158385136582185810795644204432393284934465168088766068888910973648245316527838773522153234057838176459812947,150246381581979570067867266661334447986206293190323071698511859470883839030317592725158385136582185810795644204432393284934465168088766068888910973648245316527838773522153234057838176459812948⟩,
  ⟨4173510599499432501885201851703734666283508144175640880514218318635662195286599797921066253793949605855434561234233146803735143558021279691358638156895703236884410375615367612717727123883692,4173510599499432501885201851703734666283508144175640880514218318635662195286599797921066253793949605855434561234233146803735143558021279691358638156895703236884410375615367612717727123883693⟩,
  ⟨112797583770254932483383833829830666656311030923665969743627522125288167440178372916785574426863502860957690844168463427127976852919494045712395625862046033429308388530145070613992624969829,112797583770254932483383833829830666656311030923665969743627522125288167440178372916785574426863502860957690844168463427127976852919494045712395625862046033429308388530145070613992624969830⟩,
  ⟨2968357467638287696931153521837649122534500813780683414305987424349688616846799287283830905970092180551518180109696405977052022445249843308220937522685421932350220750793291331947174341311,2968357467638287696931153521837649122534500813780683414305987424349688616846799287283830905970092180551518180109696405977052022445249843308220937522685421932350220750793291331947174341312⟩,
  ⟨76111729939443274280285987739426900577807713173863677289897113444863810688379468904713612973592107193628671284864010409668000575519226751492844551863728767496159506430597213639671136956,76111729939443274280285987739426900577807713173863677289897113444863810688379468904713612973592107193628671284864010409668000575519226751492844551863728767496159506430597213639671136957⟩,
  ⟨1902793248486081857007149693485672514445192829346591932247427836121595267209486722617840324339802679840716782121600260241700014387980668787321113796593219187403987660764930340991778423,1902793248486081857007149693485672514445192829346591932247427836121595267209486722617840324339802679840716782121600260241700014387980668787321113796593219187403987660764930340991778424⟩,
  ⟨46409591426489801390418285206967622303541288520648583713351898441990128468524066405313178642434211703432116637112201469309756448487333385056612531624224858229365552701583666853458010,46409591426489801390418285206967622303541288520648583713351898441990128468524066405313178642434211703432116637112201469309756448487333385056612531624224858229365552701583666853458011⟩,
  ⟨1104990272059280985486149647784943388179554488586871040794092820047384011155334914412218539105576469129336110407433368316898963059222223453728869800576782338794417921466277782225190,1104990272059280985486149647784943388179554488586871040794092820047384011155334914412218539105576469129336110407433368316898963059222223453728869800576782338794417921466277782225191⟩,
  ⟨25697448187425139197352317390347520655338476478764442809164949303427535143147323590981826490827359747193863032731008565509278210679586591947183018618064705553358556313169250749423,25697448187425139197352317390347520655338476478764442809164949303427535143147323590981826490827359747193863032731008565509278210679586591947183018618064705553358556313169250749424⟩,
  ⟨584032913350571345394370849780625469439510829062828245662839756896080344162439172522314238427894539708951432562068376488847232060899695271526886786774197853485421734390210244305,584032913350571345394370849780625469439510829062828245662839756896080344162439172522314238427894539708951432562068376488847232060899695271526886786774197853485421734390210244306⟩,
  ⟨12978509185568252119874907772902788209766907312507294348063105708801785425831981611606983076175434215754476279157075033085494045797771006033930817483871063410787149653115783206,12978509185568252119874907772902788209766907312507294348063105708801785425831981611606983076175434215754476279157075033085494045797771006033930817483871063410787149653115783207⟩,
  ⟨282141504034092437388584951584843221951454506793636833653545776278299683170260469817543110351639874255532093025153805067075957517342847957259365597475457900234503253328603982,282141504034092437388584951584843221951454506793636833653545776278299683170260469817543110351639874255532093025153805067075957517342847957259365597475457900234503253328603983⟩,
  ⟨6003010724129626327416701097549855786201159719013549652203101622942546450431073825905172560673188813947491340960719256746296968454103148026795012712243785111372409645289446,6003010724129626327416701097549855786201159719013549652203101622942546450431073825905172560673188813947491340960719256746296968454103148026795012712243785111372409645289447⟩
]
theorem expTable_correct : expTable =
    ((List.range 48).map (fun k => (1:ℚ)/(k.factorial:ℚ))).map (point scale) := by
  decide +kernel

def cosTable : List Box := [
  ⟨1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856,1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856⟩,
  ⟨-776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,-776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928⟩,
  ⟨64688253845862872297874145352604273135703584046529025464127168251085456361932370263786600367860269914603655445713794716923815835171450599643511969793382547466852290667535412731261053567983268534385958299738186197953868618909002410,64688253845862872297874145352604273135703584046529025464127168251085456361932370263786600367860269914603655445713794716923815835171450599643511969793382547466852290667535412731261053567983268534385958299738186197953868618909002411⟩,
  ⟨-2156275128195429076595804845086809104523452801550967515470905608369515212064412342126220012262008997153455181523793157230793861172381686654783732326446084915561743022251180424375368452266108951146198609991272873265128953963633414,-2156275128195429076595804845086809104523452801550967515470905608369515212064412342126220012262008997153455181523793157230793861172381686654783732326446084915561743022251180424375368452266108951146198609991272873265128953963633413⟩,
  ⟨38504913003489804939210800805121591152204514313410134204837600149455628786864506109396785933250160663454556812924877807692747520935387261692566648686537230635031125397342507578131579504751945556182118035558444165448731320779168,38504913003489804939210800805121591152204514313410134204837600149455628786864506109396785933250160663454556812924877807692747520935387261692566648686537230635031125397342507578131579504751945556182118035558444165448731320779169⟩,
  ⟨-427832366705442277102342231168017679468939047926779268942640001660618097631827845659964288147224007371717297921387531196586083565948747352139629429850413673722568059970472306423684216719466061735356867061760490727208125786436,-427832366705442277102342231168017679468939047926779268942640001660618097631827845659964288147224007371717297921387531196586083565948747352139629429850413673722568059970472306423684216719466061735356867061760490727208125786435⟩,
  ⟨3241154293223047553805622963394073329310144302475600522292727285307712860847180648939123395054727328573615893343844933307470330045066267819239616892806164194867939848261153836543062247874742891934521720164852202478849437776,3241154293223047553805622963394073329310144302475600522292727285307712860847180648939123395054727328573615893343844933307470330045066267819239616892806164194867939848261153836543062247874742891934521720164852202478849437777⟩,
  ⟨-17808540072654107438492433864802600710495298365250552320289710358833587147511981587577601071729271036118768644746400732458628187060803669336481411498934968103669999166270076024961880482828257647991877583323363749883788120,-17808540072654107438492433864802600710495298365250552320289710358833587147511981587577601071729271036118768644746400732458628187060803669336481411498934968103669999166270076024961880482828257647991877583323363749883788119⟩,
  ⟨74202250302725447660385141103344169627063743188543968001207126495139946447966589948240004465538629317161536019776669718577617446086681955568672547912229033765291663192791983437341168678451073533299489930514015624515783,74202250302725447660385141103344169627063743188543968001207126495139946447966589948240004465538629317161536019776669718577617446086681955568672547912229033765291663192791983437341168678451073533299489930514015624515784⟩,
  ⟨-242491014061194273399951441514196632768182167282823424840546165016797210614269901791634001521368069663926588299923757250253651784596999854799583489909245208383306088865333279206997283262912005010782646831745149099725,-242491014061194273399951441514196632768182167282823424840546165016797210614269901791634001521368069663926588299923757250253651784596999854799583489909245208383306088865333279206997283262912005010782646831745149099724⟩,
  ⟨638134247529458614210398530300517454653110966533745854843542539517887396353341846820089477687810709641912074473483571711193820485781578565262061815550645285219226549645613892649992850691873697396796439030908287104,638134247529458614210398530300517454653110966533745854843542539517887396353341846820089477687810709641912074473483571711193820485781578565262061815550645285219226549645613892649992850691873697396796439030908287105⟩,
  ⟨-1381242960020473190931598550434020464617123304185597088405936232722699992106800534242617917073183354203272888470743661712540736982211209015718748518507890227747243613951545222186131711454272072287438179720580709,-1381242960020473190931598550434020464617123304185597088405936232722699992106800534242617917073183354203272888470743661712540736982211209015718748518507890227747243613951545222186131711454272072287438179720580708⟩,
  ⟨2502251739167523896615214765279022580828121927872458493489014914352717377005073431598945501944172743121871174765839966870544813373571030825577442968311395340121818141216567431496615419301217522259851774856124,2502251739167523896615214765279022580828121927872458493489014914352717377005073431598945501944172743121871174765839966870544813373571030825577442968311395340121818141216567431496615419301217522259851774856125⟩,
  ⟨-3849618060257729071715715023506188585889418350573013066906176791311872887700112971690685387606419604802878730408984564416222789805493893577811450720479069754033566371102411433071716029694180803476695038241,-3849618060257729071715715023506188585889418350573013066906176791311872887700112971690685387606419604802878730408984564416222789805493893577811450720479069754033566371102411433071716029694180803476695038240⟩,
  ⟨5092087381293292422904384951727762679747907871128324162574307925015704877910202343506197602653994186247194087842572175153733848949065996796046892487406176923324823242198956922052534430812408470207268569,5092087381293292422904384951727762679747907871128324162574307925015704877910202343506197602653994186247194087842572175153733848949065996796046892487406176923324823242198956922052534430812408470207268570⟩,
  ⟨-5852974001486543014832626381296278942238974564515315129395756235650235491850807291386434026039073777295625388324795603624981435573639076777065393663685260831407842807125237841439694748060239620927895,-5852974001486543014832626381296278942238974564515315129395756235650235491850807291386434026039073777295625388324795603624981435573639076777065393663685260831407842807125237841439694748060239620927894⟩,
  ⟨5900175404724337716565147561790603772418321133583987025600560721421608358720571866316969784313582436789944947908060084299376447150845843525267533935166593580048228636214957501451305189576854456580,5900175404724337716565147561790603772418321133583987025600560721421608358720571866316969784313582436789944947908060084299376447150845843525267533935166593580048228636214957501451305189576854456581⟩,
  ⟨-5258623355369284952375354333146705679517220261661307509447915081480934366061115745380543479780376503377847547155133764972706280883106812411111884077688586078474357073275363192024336176093453170,-5258623355369284952375354333146705679517220261661307509447915081480934366061115745380543479780376503377847547155133764972706280883106812411111884077688586078474357073275363192024336176093453169⟩,
  ⟨4173510599499432501885201851703734666283508144175640880514218318635662195286599797921066253793949605855434561234233146803735143558021279691358638156895703236884410375615367612717727123883692,4173510599499432501885201851703734666283508144175640880514218318635662195286599797921066253793949605855434561234233146803735143558021279691358638156895703236884410375615367612717727123883693⟩,
  ⟨-2968357467638287696931153521837649122534500813780683414305987424349688616846799287283830905970092180551518180109696405977052022445249843308220937522685421932350220750793291331947174341312,-2968357467638287696931153521837649122534500813780683414305987424349688616846799287283830905970092180551518180109696405977052022445249843308220937522685421932350220750793291331947174341311⟩,
  ⟨1902793248486081857007149693485672514445192829346591932247427836121595267209486722617840324339802679840716782121600260241700014387980668787321113796593219187403987660764930340991778423,1902793248486081857007149693485672514445192829346591932247427836121595267209486722617840324339802679840716782121600260241700014387980668787321113796593219187403987660764930340991778424⟩,
  ⟨-1104990272059280985486149647784943388179554488586871040794092820047384011155334914412218539105576469129336110407433368316898963059222223453728869800576782338794417921466277782225191,-1104990272059280985486149647784943388179554488586871040794092820047384011155334914412218539105576469129336110407433368316898963059222223453728869800576782338794417921466277782225190⟩,
  ⟨584032913350571345394370849780625469439510829062828245662839756896080344162439172522314238427894539708951432562068376488847232060899695271526886786774197853485421734390210244305,584032913350571345394370849780625469439510829062828245662839756896080344162439172522314238427894539708951432562068376488847232060899695271526886786774197853485421734390210244306⟩,
  ⟨-282141504034092437388584951584843221951454506793636833653545776278299683170260469817543110351639874255532093025153805067075957517342847957259365597475457900234503253328603983,-282141504034092437388584951584843221951454506793636833653545776278299683170260469817543110351639874255532093025153805067075957517342847957259365597475457900234503253328603982⟩,
  ⟨125062723419367215154514606198955328879190827479448951087564617144636384383980704706357761680691433623906069603348317848881186842793815583891562764838412189820258534276863,125062723419367215154514606198955328879190827479448951087564617144636384383980704706357761680691433623906069603348317848881186842793815583891562764838412189820258534276864⟩,
  ⟨-51046009558925393940618206611818501583343194889571000443903925365157707911828859063819494563547523928124926368713599121992321160324006360772066434627923342783778993583,-51046009558925393940618206611818501583343194889571000443903925365157707911828859063819494563547523928124926368713599121992321160324006360772066434627923342783778993582⟩,
  ⟨19248118234888911742314557545934578274262139852779411932090469594705018066300474760112931585048085945748463939937254570886998929232279924876344809437376826087397810,19248118234888911742314557545934578274262139852779411932090469594705018066300474760112931585048085945748463939937254570886998929232279924876344809437376826087397811⟩,
  ⟨-6725408188291024368383842608642410298484325594961359864462078824145708618553625003533519072343845543587863011857880702616002421115401790662594273038915732385534,-6725408188291024368383842608642410298484325594961359864462078824145708618553625003533519072343845543587863011857880702616002421115401790662594273038915732385533⟩,
  ⟨2183574087107475444280468379429353993014391426935506449500674942904450850179748377770623075436313488177877601252558669680520266595909672293050088648998614410,2183574087107475444280468379429353993014391426935506449500674942904450850179748377770623075436313488177877601252558669680520266595909672293050088648998614411⟩,
  ⟨-660488229615086341282658311987100421359465041420298381579151525379446718142694609126020289000699784687803267166533172922117443011466930518163971158196799,-660488229615086341282658311987100421359465041420298381579151525379446718142694609126020289000699784687803267166533172922117443011466930518163971158196798⟩,
  ⟨186578595936465068158943025985056616203238712265621011745523029768205287610930680544073527966299374205594143267382252237886283336572579242419200892145,186578595936465068158943025985056616203238712265621011745523029768205287610930680544073527966299374205594143267382252237886283336572579242419200892146⟩,
  ⟨-49333314631534920190095987833172029667699289335172134253179013688050049606274637901658785818693647330934464110889014341059302838861073305769222870,-49333314631534920190095987833172029667699289335172134253179013688050049606274637901658785818693647330934464110889014341059302838861073305769222869⟩,
  ⟨12235445097106875047146822379258935929488911045429596788982890299615587699968908209736802038366479992791285741787949985381771537415940800041969,12235445097106875047146822379258935929488911045429596788982890299615587699968908209736802038366479992791285741787949985381771537415940800041970⟩,
  ⟨-2852085104220716794206718503323761288925154089843728855240766969607363100225852729542378097521324007643656350067121208713699659071314871805,-2852085104220716794206718503323761288925154089843728855240766969607363100225852729542378097521324007643656350067121208713699659071314871804⟩,
  ⟨626006388108146794163019864645250502397970607955164366821941828272028775291012451611584305865084286137764782718858913238301066521359717,626006388108146794163019864645250502397970607955164366821941828272028775291012451611584305865084286137764782718858913238301066521359718⟩,
  ⟨-129607947848477597135200800133592236521318966450344589404128742913463514553004648366787640965855959862891259362082590732567508596555,-129607947848477597135200800133592236521318966450344589404128742913463514553004648366787640965855959862891259362082590732567508596554⟩,
  ⟨25353667419498747483411737115334944546423897975419520618961021696686915992371801323706502536356799660189995962848707107309763027,25353667419498747483411737115334944546423897975419520618961021696686915992371801323706502536356799660189995962848707107309763028⟩,
  ⟨-4693385305349638556721906167222314799412050717404576197512221713566626433241725531970844601324842587965567560690245669624170,-4693385305349638556721906167222314799412050717404576197512221713566626433241725531970844601324842587965567560690245669624169⟩,
  ⟨823400930763094483635422134600406105160008897790276525879337142730987093551179917889621859881551331222029396612323801688,823400930763094483635422134600406105160008897790276525879337142730987093551179917889621859881551331222029396612323801689⟩,
  ⟨-137096392068447299972597758008725625234766716248797290356199990464699815776087232415854455524733821382289276825228739,-137096392068447299972597758008725625234766716248797290356199990464699815776087232415854455524733821382289276825228738⟩,
  ⟨21692467099437863919714835127962915385247898140632482651297466845680350597482157027825072076698389459222986839434,21692467099437863919714835127962915385247898140632482651297466845680350597482157027825072076698389459222986839435⟩,
  ⟨-3265954095067429075536711100265419359417027723672460501550356345329772748792857125538252345181931565676450895,-3265954095067429075536711100265419359417027723672460501550356345329772748792857125538252345181931565676450894⟩,
  ⟨468438625224817710203200100439675754362740637359790662872971363357683985770633552142606475212554728295532,468438625224817710203200100439675754362740637359790662872971363357683985770633552142606475212554728295533⟩,
  ⟨-64081891275624857756935718254401607983959047518439215167301144098178383826352059116635632724015694706,-64081891275624857756935718254401607983959047518439215167301144098178383826352059116635632724015694705⟩,
  ⟨8370152987934281316214174275653292578887022925605958093952605028497699036879840532475918589866208,8370152987934281316214174275653292578887022925605958093952605028497699036879840532475918589866209⟩,
  ⟨-1044962919841982686169060458883057750173161413933328101617054310673870042057408306176768862655,-1044962919841982686169060458883057750173161413933328101617054310673870042057408306176768862654⟩,
  ⟨124816402274484315118139089689806229117673365257205936647999798217136889877855746079403829,124816402274484315118139089689806229117673365257205936647999798217136889877855746079403830⟩,
  ⟨-14277785663976700425319044805514324996302146563395783190116655023694450912589309778015,-14277785663976700425319044805514324996302146563395783190116655023694450912589309778014⟩,
  ⟨1565546673681655748390246140955518091699796772302169209442615682422637161468126072,1565546673681655748390246140955518091699796772302169209442615682422637161468126073⟩,
  ⟨-164690371731712155311408178093363990290321562413440901477237079993965617659176,-164690371731712155311408178093363990290321562413440901477237079993965617659175⟩,
  ⟨16635391084011328819334159403370100029325410344792010250225967676158143197,16635391084011328819334159403370100029325410344792010250225967676158143198⟩,
  ⟨-1614772964862291673396831625254329259301631755464182707263246716769380,-1614772964862291673396831625254329259301631755464182707263246716769379⟩,
  ⟨150744302171610499756985775322472858411280036917866197466695922028,150744302171610499756985775322472858411280036917866197466695922029⟩,
  ⟨-13543962459264195845191893559970607224733156955783126457025690,-13543962459264195845191893559970607224733156955783126457025689⟩,
  ⟨1172028596336465545620620764968034546965486064017231434495,1172028596336465545620620764968034546965486064017231434496⟩,
  ⟨-97750508451748585956682298996499962215636869392596450,-97750508451748585956682298996499962215636869392596449⟩,
  ⟨7862814386401913284803917229448195158915449597216,7862814386401913284803917229448195158915449597217⟩,
  ⟨-610372177177605440521962213122822167281124795,-610372177177605440521962213122822167281124794⟩,
  ⟨45755035770435190443925203382520402344911,45755035770435190443925203382520402344912⟩,
  ⟨-3314141371174503146742373126359582960,-3314141371174503146742373126359582959⟩,
  ⟨232082729073844758175236213330503,232082729073844758175236213330504⟩,
  ⟨-15721631829958322596886344217,-15721631829958322596886344216⟩,
  ⟨1030791491604925425969469,1030791491604925425969470⟩,
  ⟨-65447078832058757205,-65447078832058757204⟩
]
theorem cosTable_correct : cosTable =
    ((List.range 64).map (fun k => (-1:ℚ)^k/((2*k).factorial:ℚ))).map (point scale) := by
  decide +kernel

def sinTable : List Box := [
  ⟨1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856,1552518092300708935148979488462502555256886017116696611139052038026050952686376886330878408828646477950487730697131073206171580044114814391444287275041181139204454976020849905550265285631598444825262999193716468750892846853816057856⟩,
  ⟨-258753015383451489191496581410417092542814336186116101856508673004341825447729481055146401471441079658414621782855178867695263340685802398574047879173530189867409162670141650925044214271933074137543833198952744791815474475636009643,-258753015383451489191496581410417092542814336186116101856508673004341825447729481055146401471441079658414621782855178867695263340685802398574047879173530189867409162670141650925044214271933074137543833198952744791815474475636009642⟩,
  ⟨12937650769172574459574829070520854627140716809305805092825433650217091272386474052757320073572053982920731089142758943384763167034290119928702393958676509493370458133507082546252210713596653706877191659947637239590773723781800482,12937650769172574459574829070520854627140716809305805092825433650217091272386474052757320073572053982920731089142758943384763167034290119928702393958676509493370458133507082546252210713596653706877191659947637239590773723781800483⟩,
  ⟨-308039304027918439513686406440972729217636114507281073638700801195645030294916048875174287466001285307636454503399022461541980167483098093540533189492297845080249003178740060625052636038015564449456944284467553323589850566233345,-308039304027918439513686406440972729217636114507281073638700801195645030294916048875174287466001285307636454503399022461541980167483098093540533189492297845080249003178740060625052636038015564449456944284467553323589850566233344⟩,
  ⟨4278323667054422771023422311680176794689390479267792689426400016606180976318278456599642881472240073717172979213875311965860835659487473521396294298504136737225680599704723064236842167194660617353568670617604907272081257864352,4278323667054422771023422311680176794689390479267792689426400016606180976318278456599642881472240073717172979213875311965860835659487473521396294298504136737225680599704723064236842167194660617353568670617604907272081257864353⟩,
  ⟨-38893851518676570645667475560728879951721731629707206267512727423692554330166167787269480740656727942883390720126139199689643960540795213830875402713673970338415278179133846038516746974496914703214260641978226429746193253313,-38893851518676570645667475560728879951721731629707206267512727423692554330166167787269480740656727942883390720126139199689643960540795213830875402713673970338415278179133846038516746974496914703214260641978226429746193253312⟩,
  ⟨249319561017157504138894074107236409946934177113507732484055945023670220065167742226086415004209794505662761026449610254420794618851251370710739760985089553451379988327781064349466326759595607071886286166527092498373033675,249319561017157504138894074107236409946934177113507732484055945023670220065167742226086415004209794505662761026449610254420794618851251370710739760985089553451379988327781064349466326759595607071886286166527092498373033676⟩,
  ⟨-1187236004843607162566162257653506714033019891016703488019314023922239143167465439171840071448618069074584576316426715497241879137386911289098760766595664540244666611084671734997458698855217176532791838888224249992252542,-1187236004843607162566162257653506714033019891016703488019314023922239143167465439171840071448618069074584576316426715497241879137386911289098760766595664540244666611084671734997458698855217176532791838888224249992252541⟩,
  ⟨4364838253101496921199125947255539389827279011090821647129830970302349791056858232249412027384625253950678589398627630504565732122745997386392502818366413750899509599575999025725951098732416090194087642971412683795046,4364838253101496921199125947255539389827279011090821647129830970302349791056858232249412027384625253950678589398627630504565732122745997386392502818366413750899509599575999025725951098732416090194087642971412683795047⟩,
  ⟨-12762684950589172284207970606010349093062219330674917096870850790357747927066836936401789553756214192838241489469671434223876409715631571305241236311012905704384530992912277852999857013837473947935928780618165742091,-12762684950589172284207970606010349093062219330674917096870850790357747927066836936401789553756214192838241489469671434223876409715631571305241236311012905704384530992912277852999857013837473947935928780618165742090⟩,
  ⟨30387345120450410200495168109548450221576712692083135944930597119899399826349611753337594175610033792472003546356360557675896213608646598345812467407173585010439359506933994888094897651993985590323639953852775576,30387345120450410200495168109548450221576712692083135944930597119899399826349611753337594175610033792472003546356360557675896213608646598345812467407173585010439359506933994888094897651993985590323639953852775577⟩,
  ⟨-60054041740020573518765154366696541939874926268939003843736357944465217048121762358374692046660145834924908194380159204893075520965704739813858631239473488162923635389197618355918770063229220534236442596546988,-60054041740020573518765154366696541939874926268939003843736357944465217048121762358374692046660145834924908194380159204893075520965704739813858631239473488162923635389197618355918770063229220534236442596546987⟩,
  ⟨100090069566700955864608590611160903233124877114898339739560596574108695080202937263957820077766909724874846990633598674821792534942841233023097718732455813604872725648662697259864616772048700890394070994244,100090069566700955864608590611160903233124877114898339739560596574108695080202937263957820077766909724874846990633598674821792534942841233023097718732455813604872725648662697259864616772048700890394070994245⟩,
  ⟨-142578446676212187841322778648377355032941420391593076552080621900439736581485665618173532874311837214921434459592020904304547770573847910289312989647372953853095050781570793817470964062747437165803519935,-142578446676212187841322778648377355032941420391593076552080621900439736581485665618173532874311837214921434459592020904304547770573847910289312989647372953853095050781570793817470964062747437165803519934⟩,
  ⟨175589220044596290444978791438888368267169236935459453881872687069507064755524218741593020781172213318868761649743868108749443067209172303311961809910557824942235284213757135243190842441807188627836847,175589220044596290444978791438888368267169236935459453881872687069507064755524218741593020781172213318868761649743868108749443067209172303311961809910557824942235284213757135243190842441807188627836848⟩,
  ⟨-188805612951178806930084721977299320717386276274687584819217943085491467479058299722143033098034637977278238333057922697580046308827066992808561085925330994561543316358878640046441766066459342610578,-188805612951178806930084721977299320717386276274687584819217943085491467479058299722143033098034637977278238333057922697580046308827066992808561085925330994561543316358878640046441766066459342610577⟩,
  ⟨178793194082555688380762047326987993103585488896484455321229112770351768446077935342938478312532801114846816603274548009072013550025631621977804058641411926668128140491362348528827429987177407775,178793194082555688380762047326987993103585488896484455321229112770351768446077935342938478312532801114846816603274548009072013550025631621977804058641411926668128140491362348528827429987177407776⟩,
  ⟨-150246381581979570067867266661334447986206293190323071698511859470883839030317592725158385136582185810795644204432393284934465168088766068888910973648245316527838773522153234057838176459812948,-150246381581979570067867266661334447986206293190323071698511859470883839030317592725158385136582185810795644204432393284934465168088766068888910973648245316527838773522153234057838176459812947⟩,
  ⟨112797583770254932483383833829830666656311030923665969743627522125288167440178372916785574426863502860957690844168463427127976852919494045712395625862046033429308388530145070613992624969829,112797583770254932483383833829830666656311030923665969743627522125288167440178372916785574426863502860957690844168463427127976852919494045712395625862046033429308388530145070613992624969830⟩,
  ⟨-76111729939443274280285987739426900577807713173863677289897113444863810688379468904713612973592107193628671284864010409668000575519226751492844551863728767496159506430597213639671136957,-76111729939443274280285987739426900577807713173863677289897113444863810688379468904713612973592107193628671284864010409668000575519226751492844551863728767496159506430597213639671136956⟩,
  ⟨46409591426489801390418285206967622303541288520648583713351898441990128468524066405313178642434211703432116637112201469309756448487333385056612531624224858229365552701583666853458010,46409591426489801390418285206967622303541288520648583713351898441990128468524066405313178642434211703432116637112201469309756448487333385056612531624224858229365552701583666853458011⟩,
  ⟨-25697448187425139197352317390347520655338476478764442809164949303427535143147323590981826490827359747193863032731008565509278210679586591947183018618064705553358556313169250749424,-25697448187425139197352317390347520655338476478764442809164949303427535143147323590981826490827359747193863032731008565509278210679586591947183018618064705553358556313169250749423⟩,
  ⟨12978509185568252119874907772902788209766907312507294348063105708801785425831981611606983076175434215754476279157075033085494045797771006033930817483871063410787149653115783206,12978509185568252119874907772902788209766907312507294348063105708801785425831981611606983076175434215754476279157075033085494045797771006033930817483871063410787149653115783207⟩,
  ⟨-6003010724129626327416701097549855786201159719013549652203101622942546450431073825905172560673188813947491340960719256746296968454103148026795012712243785111372409645289447,-6003010724129626327416701097549855786201159719013549652203101622942546450431073825905172560673188813947491340960719256746296968454103148026795012712243785111372409645289446⟩,
  ⟨2552300477946269697030910330590925079167159744478550022195196268257885395591442953190974728177376196406246318435679956099616058016200318038603321731396167139188949679119,2552300477946269697030910330590925079167159744478550022195196268257885395591442953190974728177376196406246318435679956099616058016200318038603321731396167139188949679120⟩,
  ⟨-1000902148214223410600356992388598070261631272344529420468704418924660939447624687525872442422500469178920124876737237686123944320078556093569930090743594956544686149,-1000902148214223410600356992388598070261631272344529420468704418924660939447624687525872442422500469178920124876737237686123944320078556093569930090743594956544686148⟩,
  ⟨363172042167715315892727500866690156118153582127913432680952256503868265401895750190810029906567659353744602640325557941264130740231696695780090744101449548818826,363172042167715315892727500866690156118153582127913432680952256503868265401895750190810029906567659353744602640325557941264130740231696695780090744101449548818827⟩,
  ⟨-122280148878018624879706229248043823608805919908388361172037796802649247610065909155154892224433555337961145670143285502109134929370941648410804964343922407010,-122280148878018624879706229248043823608805919908388361172037796802649247610065909155154892224433555337961145670143285502109134929370941648410804964343922407009⟩,
  ⟨38308317317675007794394182095251824438848972402377306131590788472007909652276287329309176762040587511892589495658924029482811694665081970053510327175414287,38308317317675007794394182095251824438848972402377306131590788472007909652276287329309176762040587511892589495658924029482811694665081970053510327175414288⟩,
  ⟨-11194715756187904089536581559103396972194322735937260704731381786092317256655840832644411677977962452335648596042935134273177000194354754545152053528760,-11194715756187904089536581559103396972194322735937260704731381786092317256655840832644411677977962452335648596042935134273177000194354754545152053528759⟩,
  ⟨3058665507155165051785951245656665839397355938780672323697098848659103075589027549902844720759006134517936774875118889145676776009386544957691817904,3058665507155165051785951245656665839397355938780672323697098848659103075589027549902844720759006134517936774875118889145676776009386544957691817905⟩,
  ⟨-783068486214840003017396632272571899487290306907494194494904979175397612798010125423155330455454719538642287474428799064433378394620211202686078,-783068486214840003017396632272571899487290306907494194494904979175397612798010125423155330455454719538642287474428799064433378394620211202686077⟩,
  ⟨188237616878567308417643421219368245069060169929686104445890619994085964614906280149796954436407384504481319104429999775104177498706781539107,188237616878567308417643421219368245069060169929686104445890619994085964614906280149796954436407384504481319104429999775104177498706781539108⟩,
  ⟨-42568434391353982003085350795877034163062001340951176943892044322497956719788846709587732798825731457368005224882406100204472523452460774,-42568434391353982003085350795877034163062001340951176943892044322497956719788846709587732798825731457368005224882406100204472523452460773⟩,
  ⟨9072556349393431799464056009351456556492327651524121258289012003942446018710325385675134867609917190402388155345781351279725601758836,9072556349393431799464056009351456556492327651524121258289012003942446018710325385675134867609917190402388155345781351279725601758837⟩,
  ⟨-1825464054203909818805645072304116007342520654230205484565193562161457951450769695306868182617689575533679709325106911726302937980,-1825464054203909818805645072304116007342520654230205484565193562161457951450769695306868182617689575533679709325106911726302937979⟩,
  ⟨347310512595873253197421056374451295156491753087938638615904406803930356059887689365842500498038351509451999491078179552188534,347310512595873253197421056374451295156491753087938638615904406803930356059887689365842500498038351509451999491078179552188535⟩,
  ⟨-62578470737995180756292082229630863992160676232061015966829622847555019109889673759611261350997901172874234142536608928323,-62578470737995180756292082229630863992160676232061015966829622847555019109889673759611261350997901172874234142536608928322⟩,
  ⟨10693518581338889397862625124680598768311803867406188647783599256246585630534804128436647530929238067818563592367841580,10693518581338889397862625124680598768311803867406188647783599256246585630534804128436647530929238067818563592367841581⟩,
  ⟨-1735397367955029113577186810237033230819831851250598612103797347654428047798572562226005766135871156737838947154795,-1735397367955029113577186810237033230819831851250598612103797347654428047798572562226005766135871156737838947154794⟩,
  ⟨267808235795529184194010310221764387472196273341141761127129220317041365401014284294136692304918388385468973326,267808235795529184194010310221764387472196273341141761127129220317041365401014284294136692304918388385468973327⟩,
  ⟨-39348844518884687657068808436932763366470213538222415681329594522045454804733218379978943917854597176824710,-39348844518884687657068808436932763366470213538222415681329594522045454804733218379978943917854597176824709⟩,
  ⟨5511042649703737767096471769878538286620478086585772504387898392443341009066277084030664414265349744653,5511042649703737767096471769878538286620478086585772504387898392443341009066277084030664414265349744654⟩,
  ⟨-736573462938216755826847336257489746942058017453324312267829242507797515245425966857880835908226376,-736573462938216755826847336257489746942058017453324312267829242507797515245425966857880835908226375⟩,
  ⟨94046662785778441755215441299475197515584527253999529145534887960648303785166747555909197638946,94046662785778441755215441299475197515584527253999529145534887960648303785166747555909197638947⟩,
  ⟨-11483109009252556990868796251462173078825949603662946171615981435976593868762728639305152337,-11483109009252556990868796251462173078825949603662946171615981435976593868762728639305152336⟩,
  ⟨1342111852413809839979990211718346549652401776959203619870965572227278385783395119133374,1342111852413809839979990211718346549652401776959203619870965572227278385783395119133375⟩,
  ⟨-150292480673438951845463629531729736803180490141008244106491105512573167500940102927,-150292480673438951845463629531729736803180490141008244106491105512573167500940102926⟩,
  ⟨16139656429707791220518001453149671048451513116517208344769233839408630530599237,16139656429707791220518001453149671048451513116517208344769233839408630530599238⟩,
  ⟨-1663539108401132881933415940337010002932541034479201025022596767615814319790,-1663539108401132881933415940337010002932541034479201025022596767615814319789⟩,
  ⟨164706842415953750686476825775941584448766439057346636140851165110476665,164706842415953750686476825775941584448766439057346636140851165110476666⟩,
  ⟨-15677407425847491974726520633537177274773123839458084536536375890965,-15677407425847491974726520633537177274773123839458084536536375890964⟩,
  ⟨1435660020682004759590340717356884365821714637313011404444723066,1435660020682004759590340717356884365821714637313011404444723067⟩,
  ⟨-126579088404338278927027042616547731072272494913860994925474,-126579088404338278927027042616547731072272494913860994925473⟩,
  ⟨10752555929692344455235052889614995843720055633185609490,10752555929692344455235052889614995843720055633185609491⟩,
  ⟨-880635211277014287898038729698197857798530354888257,-880635211277014287898038729698197857798530354888256⟩,
  ⟨69582428198247020219503692296001727070048226524,69582428198247020219503692296001727070048226525⟩,
  ⟨-5307584149370482091495323592372366672009781,-5307584149370482091495323592372366672009780⟩,
  ⟨391068681798591371315600028910430789272,391068681798591371315600028910430789273⟩,
  ⟨-27849927488861370981028345599660362,-27849927488861370981028345599660361⟩,
  ⟨1918039083254915356820133994466,1918039083254915356820133994467⟩,
  ⟨-127818144959010752820214181,-127818144959010752820214180⟩,
  ⟨8246331932839403407755,8246331932839403407756⟩,
  ⟨-515331329386289427,-515331329386289426⟩
]
theorem sinTable_correct : sinTable =
    ((List.range 64).map (fun k => (-1:ℚ)^k/((2*k+1).factorial:ℚ))).map (point scale) := by
  decide +kernel

def z0Table : List Box := [
  ⟨1380016082045074609021315100855557826895009792992619209901379589356489735721223898960780807847685758178211316175227620627708071150324279459061588688925494345959515534240755471600235809450309728733567110394414638889682530536725384760,1380016082045074609021315100855557826895009792992619209901379589356489735721223898960780807847685758178211316175227620627708071150324279459061588688925494345959515534240755471600235809450309728733567110394414638889682530536725384761⟩,
  ⟨709722556480324084639533480440001168117433607824775593663566645954766149799486576608401558321666961348794391175831347751392722305881058007517388468590254235064893703323817099680121273431587860491548799631413242857551015704601626448,709722556480324084639533480440001168117433607824775593663566645954766149799486576608401558321666961348794391175831347751392722305881058007517388468590254235064893703323817099680121273431587860491548799631413242857551015704601626449⟩,
  ⟨276003216409014921804263020171111565379001958598523841980275917871297947144244779792156161569537151635642263235045524125541614230064855891812317737785098869191903106848151094320047161890061945746713422078882927777936506107345076952,276003216409014921804263020171111565379001958598523841980275917871297947144244779792156161569537151635642263235045524125541614230064855891812317737785098869191903106848151094320047161890061945746713422078882927777936506107345076953⟩,
  ⟨87620068701274578350559688943210020755238717015404394279452672340094586394998342791160686212551476709727702614300166389060829914306303457718196107233364720378381938681952728355570527584146649443401086374248548500932224161061929191,87620068701274578350559688943210020755238717015404394279452672340094586394998342791160686212551476709727702614300166389060829914306303457718196107233364720378381938681952728355570527584146649443401086374248548500932224161061929192⟩,
  ⟨23657418549344136154651116014666705603914453594159186455452221531825538326649552553613385277388898711626479705861044925046424076862701933583912948953008474502163123444127236656004042447719595349718293321047108095251700523486720881,23657418549344136154651116014666705603914453594159186455452221531825538326649552553613385277388898711626479705861044925046424076862701933583912948953008474502163123444127236656004042447719595349718293321047108095251700523486720882⟩,
  ⟨5575822553717473167762889296386092229878827446434825090510624603460564588772621813982952758980548517891762893637283315667507358183128401854794297733032300387715214279760628168081760846263877691852796405633998540968414264794850039,5575822553717473167762889296386092229878827446434825090510624603460564588772621813982952758980548517891762893637283315667507358183128401854794297733032300387715214279760628168081760846263877691852796405633998540968414264794850040⟩,
  ⟨1168267582683661044674129185909466943403182893538725257059368964534594485266644570548809149500686356129702701524002218520811065524084046102909281429778196271711759182426036378074273701121955325912014484989980646679096322147492389,1168267582683661044674129185909466943403182893538725257059368964534594485266644570548809149500686356129702701524002218520811065524084046102909281429778196271711759182426036378074273701121955325912014484989980646679096322147492390⟩,
  ⟨220581991136075861581828587549339912390810756122696377207013720576461895819576247586138790465164556751762048539496922378055236147903980732717137053174904191162360125353167707748289440071977579018352385277828513708640564321554507,220581991136075861581828587549339912390810756122696377207013720576461895819576247586138790465164556751762048539496922378055236147903980732717137053174904191162360125353167707748289440071977579018352385277828513708640564321554508⟩,
  ⟨37930765671547436515393804737320355305298145894114456398031459887486833937228719823013284074697608965250087711818253848078281348184546951393158487979811567263368804624221960327086808477985562529610859902272098918152477991801700,37930765671547436515393804737320355305298145894114456398031459887486833937228719823013284074697608965250087711818253848078281348184546951393158487979811567263368804624221960327086808477985562529610859902272098918152477991801701⟩,
  ⟨5991115808634159203457072748253676632836835351480642343894199818126125565469972156660559741029160800665142059097447274465697771918379723604662981691170237290829534268851468605509095903189514491856484538410157162456904216140986,5991115808634159203457072748253676632836835351480642343894199818126125565469972156660559741029160800665142059097447274465697771918379723604662981691170237290829534268851468605509095903189514491856484538410157162456904216140987⟩,
  ⟨875325361651094688816780109322777430122264905248795147646879843557388475474508918992614247877637129967309716426575088801806492650412621955226734337995651552231587799020506776778926349491974519914096766975509975034287953656962,875325361651094688816780109322777430122264905248795147646879843557388475474508918992614247877637129967309716426575088801806492650412621955226734337995651552231587799020506776778926349491974519914096766975509975034287953656963⟩,
  ⟨118998480538188036126725661921005036251915751824672804385981050627409675097188140621218146116698381067451255566488639523382843445284853180841281530917055897296843308625010071614389987381915490288975246752226192684399930954672,118998480538188036126725661921005036251915751824672804385981050627409675097188140621218146116698381067451255566488639523382843445284853180841281530917055897296843308625010071614389987381915490288975246752226192684399930954673⟩,
  ⟨15129080324833735362265335222862819779890998362324854403773231863954862539065586254193332679366567678447328432064260794105297403834292231324906519422147063865731147143564314660376504806034127504688092268712518087012384384194,15129080324833735362265335222862819779890998362324854403773231863954862539065586254193332679366567678447328432064260794105297403834292231324906519422147063865731147143564314660376504806034127504688092268712518087012384384195⟩,
  ⟨1806657093191113908806563693132667554431919309079040552418740647177272395200224807002299789221129267218389507588390276164719283076187042219250225671817650262603896386007237929368269039199121816128166701703838957759108263481,1806657093191113908806563693132667554431919309079040552418740647177272395200224807002299789221129267218389507588390276164719283076187042219250225671817650262603896386007237929368269039199121816128166701703838957759108263482⟩,
  ⟨203416206048184677139701986189752198721223507392603084420480428422922521533654941232851531823416036012737189002544682945953578538948466975797062446012061362900586852350444566862205106635752974852949139747395201169914411888,203416206048184677139701986189752198721223507392603084420480428422922521533654941232851531823416036012737189002544682945953578538948466975797062446012061362900586852350444566862205106635752974852949139747395201169914411889⟩,
  ⟨21667139741974558341948206549033755502887215699713361122482251147805030489173771935830050382193437419903084041624433647125381172695012146544799884600282225371616394047353118024169716872229326895364256740010767041908176704,21667139741974558341948206549033755502887215699713361122482251147805030489173771935830050382193437419903084041624433647125381172695012146544799884600282225371616394047353118024169716872229326895364256740010767041908176705⟩,
  ⟨2189887385686198677341289325009294005372023404944291578689382602639118054788151281214908835419550626931381221319260940805720343122650960265757849299172909409216844104251197490143356411150450686215959638428895706374676683,2189887385686198677341289325009294005372023404944291578689382602639118054788151281214908835419550626931381221319260940805720343122650960265757849299172909409216844104251197490143356411150450686215959638428895706374676684⟩,
  ⟨210575782658576270330954437049432917930873196058595325487039780976110270738773231089908418036662563160183425468472756672829791448186818815524909364401719837371207921687830814557148143515272230696634720235398758975066678,210575782658576270330954437049432917930873196058595325487039780976110270738773231089908418036662563160183425468472756672829791448186818815524909364401719837371207921687830814557148143515272230696634720235398758975066679⟩,
  ⟨19311176240619035955390558421598712569418195810796222034297906548845838225645073026586497666839070784227347630681313410985188210958121342731550699287239060046003916263238073105320603272931663899611637023182501819882510,19311176240619035955390558421598712569418195810796222034297906548845838225645073026586497666839070784227347630681313410985188210958121342731550699287239060046003916263238073105320603272931663899611637023182501819882511⟩,
  ⟨1692666578308172890698581120780130632171612293676747113962807808803183037517411618330364317232502900043579687976240340719397366664850983780295922163611910654467125877682085016535927660792618887896393923423301029081875,1692666578308172890698581120780130632171612293676747113962807808803183037517411618330364317232502900043579687976240340719397366664850983780295922163611910654467125877682085016535927660792618887896393923423301029081876⟩,
  ⟨142088922171778859872438891396378487132842912320239760787476235476457672563274784811004330659016574332107574540130065231329144027116611886319102135223832548833473631368306892413730191305851707622560539969904695664687,142088922171778859872438891396378487132842912320239760787476235476457672563274784811004330659016574332107574540130065231329144027116611886319102135223832548833473631368306892413730191305851707622560539969904695664688⟩,
  ⟨11443659994440910195786997583169607448544116036027390835139500177093830059641524756495702321089819723986576373737074613917148569456664499396474488466512035582817135563400339617967764902478023051621710828552593671041,11443659994440910195786997583169607448544116036027390835139500177093830059641524756495702321089819723986576373737074613917148569456664499396474488466512035582817135563400339617967764902478023051621710828552593671042⟩,
  ⟨885749125226673412191826855457943815893046726152143963350501208164930945848985671549117905406856567265086178951460146896597261467739918252378818505291423681039835624114120887773902491257257398166611158253951349598,885749125226673412191826855457943815893046726152143963350501208164930945848985671549117905406856567265086178951460146896597261467739918252378818505291423681039835624114120887773902491257257398166611158253951349599⟩,
  ⟨65988121291897763786108854706317653376450905524318941501208050842427805672018941047720576179736015015491733212646030526566420075289265940470963490177096272533831943048093297301163446560246932600747957724325877471,65988121291897763786108854706317653376450905524318941501208050842427805672018941047720576179736015015491733212646030526566420075289265940470963490177096272533831943048093297301163446560246932600747957724325877472⟩,
  ⟨4738575567056277513783435852244143871032760263365379227801035270018149093019264909522029946621043363969596842127153049241055308263629192296676806818431484713381836672215461539531165591088208302948948583251591582,4738575567056277513783435852244143871032760263365379227801035270018149093019264909522029946621043363969596842127153049241055308263629192296676806818431484713381836672215461539531165591088208302948948583251591583⟩,
  ⟨328420142835251543267269875957709979938096672655596575213385690828672949888389199684507936747073254454981898016855820132219970881623996385754104006411354720444877873234750051084131439101689802805565872545032016,328420142835251543267269875957709979938096672655596575213385690828672949888389199684507936747073254454981898016855820132219970881623996385754104006411354720444877873234750051084131439101689802805565872545032017⟩,
  ⟨21996040430632587928702951568772551125483635174772980500402683614142601890672980349240192059912005005163911070882010175522140025096421980156987830059032090844610647682697765767054482186748977533582652574775292,21996040430632587928702951568772551125483635174772980500402683614142601890672980349240192059912005005163911070882010175522140025096421980156987830059032090844610647682697765767054482186748977533582652574775293⟩,
  ⟨1425242669992112944968324190463687155735847887319461381397408908945980628022938539596068861304171250160041158621596525826319364843560927076224319668676286852660150890206921284166077326442050771621610221295312,1425242669992112944968324190463687155735847887319461381397408908945980628022938539596068861304171250160041158621596525826319364843560927076224319668676286852660150890206921284166077326442050771621610221295313⟩,
  ⟨89439036719839744898493974934016879068109115646948958391444904909769321865029738476173185388636507204515767433784264741889970283666665682394908498478037777898931882689202083628576099973227070480818592741021,89439036719839744898493974934016879068109115646948958391444904909769321865029738476173185388636507204515767433784264741889970283666665682394908498478037777898931882689202083628576099973227070480818592741022⟩,
  ⟨5441197385437869617489907623691416481257547353066909214694541401148448210432400828507159445865678418098679300156341416332007427358422258542235703168591735521239492314829379286840935605874824374417477445831,5441197385437869617489907623691416481257547353066909214694541401148448210432400828507159445865678418098679300156341416332007427358422258542235703168591735521239492314829379286840935605874824374417477445832⟩,
  ⟨321217640295720744865522693365717186327664612873441825872753867240473434307626445705672495222936950678395573275095002440008871950317991227456461498462088540153290712239558549507792951643464226193736808946,321217640295720744865522693365717186327664612873441825872753867240473434307626445705672495222936950678395573275095002440008871950317991227456461498462088540153290712239558549507792951643464226193736808947⟩,
  ⟨18417304858654258923756803075215830953535982630002359514325849144868843627290551037564619899847929411483298313263169058819041499854139651458411016417613956838904892188252681313477703984190902544312708929,18417304858654258923756803075215830953535982630002359514325849144868843627290551037564619899847929411483298313263169058819041499854139651458411016417613956838904892188252681313477703984190902544312708930⟩,
  ⟨1026447346809633959156745448725036121723740304294832902224965365242114357749934131014366996013144391265549764224927639375968199841241701290744331855987876914023673328585055515344451161266708993476226645,1026447346809633959156745448725036121723740304294832902224965365242114357749934131014366996013144391265549764224927639375968199841241701290744331855987876914023673328585055515344451161266708993476226646⟩,
  ⟨55651011832245451293403100028710531241799135979459775792230399729811752305548587267095026892400719105751138821049030221761758827151419131575963530572087411668969284864788383490608619480849658037722939,55651011832245451293403100028710531241799135979459775792230399729811752305548587267095026892400719105751138821049030221761758827151419131575963530572087411668969284864788383490608619480849658037722940⟩,
  ⟨2937369195957617053230750091740961874567142365231636286176371474460740610413166034699301419433481564829872139276422497419304864410548588749347849508391380676061386313915898136120845930492966912968534,2937369195957617053230750091740961874567142365231636286176371474460740610413166034699301419433481564829872139276422497419304864410548588749347849508391380676061386313915898136120845930492966912968535⟩,
  ⟨151042540824726330303019600297985670709449332935265850307172183385515117205596752531268365671654253212014827535581450079236022490709885044438705346133668383036997142123394108868697518488277083982816,151042540824726330303019600297985670709449332935265850307172183385515117205596752531268365671654253212014827535581450079236022490709885044438705346133668383036997142123394108868697518488277083982817⟩,
  ⟨7571566235679653237197700684178303570312807616253030720031346902015204395312732961509527468353839334115801200142725200239695078524002602935505242254705770295097861886365766461307295167462538508533,7571566235679653237197700684178303570312807616253030720031346902015204395312732961509527468353839334115801200142725200239695078524002602935505242254705770295097861886365766461307295167462538508534⟩,
  ⟨370248843002157566424749491616683919400912884002223014580748909618798841673053007461940054129133618810092914763524610502212751548566028707297894940239664798142230580943580782267706047834243009134,370248843002157566424749491616683919400912884002223014580748909618798841673053007461940054129133618810092914763524610502212751548566028707297894940239664798142230580943580782267706047834243009135⟩,
  ⟨17671994948487929133382426617290940763946335899762004247943393399498668211723031769190167973751521377327112148775178434449049080462137012336340861838501039316367981996419107156744766407894826720,17671994948487929133382426617290940763946335899762004247943393399498668211723031769190167973751521377327112148775178434449049080462137012336340861838501039316367981996419107156744766407894826721⟩,
  ⟨823779816203416644873950842831856773595844701890714616622477563118749288215719620455272946373326732937935667090191780251836809848932691737849067564771469636349556576783981119141280583975252387,823779816203416644873950842831856773595844701890714616622477563118749288215719620455272946373326732937935667090191780251836809848932691737849067564771469636349556576783981119141280583975252388⟩,
  ⟨37523952873432407664411623757645071389572604033872809828797903072747424918724334393629274767318700598975667858875505270316484397341241381098398189950305543543349607879150783649306379632537043,37523952873432407664411623757645071389572604033872809828797903072747424918724334393629274767318700598975667858875505270316484397341241381098398189950305543543349607879150783649306379632537044⟩,
  ⟨1671110633426754527979425684850207164439369825036596146377625853380488719784683855242569075532058759085306113359354934699673671911313192655918757620662036814786570401552634246500687130770196,1671110633426754527979425684850207164439369825036596146377625853380488719784683855242569075532058759085306113359354934699673671911313192655918757620662036814786570401552634246500687130770197⟩,
  ⟨72797792170680155962703326513949873948024452270299983794846020070585833175655675190462437820195009980376075211222320630243620523942443596487192255635513400172283189889005047644156997523440,72797792170680155962703326513949873948024452270299983794846020070585833175655675190462437820195009980376075211222320630243620523942443596487192255635513400172283189889005047644156997523441⟩,
  ⟨3103525659982416943896087815697543278090490997983814885660352176064133731879687727695078863372305324233456804489010629639723292379814435092810469983276930177478618603407628447309420807852,3103525659982416943896087815697543278090490997983814885660352176064133731879687727695078863372305324233456804489010629639723292379814435092810469983276930177478618603407628447309420807853⟩,
  ⟨129543459955562366510032998825597454607703087212139236153304329719417730215866965522679773297058818533744659950337591837184005574520402531466570358190855567037718635779273972596952490757,129543459955562366510032998825597454607703087212139236153304329719417730215866965522679773297058818533744659950337591837184005574520402531466570358190855567037718635779273972596952490758⟩,
  ⟨5296503486534988974695574703623258317728869894888863457735532036129785235960251387133939962908436827849399775271732011367719489537083458582501528293900352880954795728400818337819272983,5296503486534988974695574703623258317728869894888863457735532036129785235960251387133939962908436827849399775271732011367719489537083458582501528293900352880954795728400818337819272984⟩,
  ⟨212206882733840474796313696799832019014734427212568539190451430841992050043055571124449836811781560631347473811214402026647746487508679322585331280907824285639563665190265192978421935,212206882733840474796313696799832019014734427212568539190451430841992050043055571124449836811781560631347473811214402026647746487508679322585331280907824285639563665190265192978421936⟩,
  ⟨8334923190372202641833260874429214213366989156147870234573779840075776043743149513273803554637122587382435615843110993400827137288385049234606981498229379082032436473436855834705560,8334923190372202641833260874429214213366989156147870234573779840075776043743149513273803554637122587382435615843110993400827137288385049234606981498229379082032436473436855834705561⟩
]
def z1Table : List Box := [
  ⟨709722556480324084639533480440001168117433607824775593663566645954766149799486576608401558321666961348794391175831347751392722305881058007517388468590254235064893703323817099680121273431587860491548799631413242857551015704601626448,709722556480324084639533480440001168117433607824775593663566645954766149799486576608401558321666961348794391175831347751392722305881058007517388468590254235064893703323817099680121273431587860491548799631413242857551015704601626449⟩,
  ⟨552006432818029843608526040342223130758003917197047683960551835742595894288489559584312323139074303271284526470091048251083228460129711783624635475570197738383806213696302188640094323780123891493426844157765855555873012214690153904,552006432818029843608526040342223130758003917197047683960551835742595894288489559584312323139074303271284526470091048251083228460129711783624635475570197738383806213696302188640094323780123891493426844157765855555873012214690153905⟩,
  ⟨262860206103823735051679066829630062265716151046213182838358017020283759184995028373482058637654430129183107842900499167182489742918910373154588321700094161135145816045858185066711582752439948330203259122745645502796672483185787573,262860206103823735051679066829630062265716151046213182838358017020283759184995028373482058637654430129183107842900499167182489742918910373154588321700094161135145816045858185066711582752439948330203259122745645502796672483185787574⟩,
  ⟨94629674197376544618604464058666822415657814376636745821808886127302153306598210214453541109555594846505918823444179700185696307450807734335651795812033898008652493776508946624016169790878381398873173284188432381006802093946883526,94629674197376544618604464058666822415657814376636745821808886127302153306598210214453541109555594846505918823444179700185696307450807734335651795812033898008652493776508946624016169790878381398873173284188432381006802093946883527⟩,
  ⟨27879112768587365838814446481930461149394137232174125452553123017302822943863109069914763794902742589458814468186416578337536790915642009273971488665161501938576071398803140840408804231319388459263982028169992704842071323974250197,27879112768587365838814446481930461149394137232174125452553123017302822943863109069914763794902742589458814468186416578337536790915642009273971488665161501938576071398803140840408804231319388459263982028169992704842071323974250198⟩,
  ⟨7009605496101966268044775115456801660419097361232351542356213787207566911599867423292854897004118136778216209144013311124866393144504276617455688578669177630270555094556218268445642206731731955472086909939883880074577932884954335,7009605496101966268044775115456801660419097361232351542356213787207566911599867423292854897004118136778216209144013311124866393144504276617455688578669177630270555094556218268445642206731731955472086909939883880074577932884954336⟩,
  ⟨1544073937952531031072800112845379386735675292858874640449096044035233270737033733102971533256151897262334339776478456646386653035327865129019959372224329338136520877472173954238026080503843053128466696944799595960483950250881549,1544073937952531031072800112845379386735675292858874640449096044035233270737033733102971533256151897262334339776478456646386653035327865129019959372224329338136520877472173954238026080503843053128466696944799595960483950250881550⟩,
  ⟨303446125372379492123150437898562842442385167152915651184251679099894671497829758584106272597580871722000701694546030784626250785476375611145267903838492538106950436993775682616694467823884500236886879218176791345219823934413607,303446125372379492123150437898562842442385167152915651184251679099894671497829758584106272597580871722000701694546030784626250785476375611145267903838492538106950436993775682616694467823884500236886879218176791345219823934413608⟩,
  ⟨53920042277707432831113654734283089695531518163325781095047798363135130089229749409945037669262447205986278531877025470191279947265417512441966835220532135617465808419663217449581863128705630426708360845691414462112137945268879,53920042277707432831113654734283089695531518163325781095047798363135130089229749409945037669262447205986278531877025470191279947265417512441966835220532135617465808419663217449581863128705630426708360845691414462112137945268880⟩,
  ⟨8753253616510946888167801093227774301222649052487951476468798435573884754745089189926142478776371299673097164265750888018064926504126219552267343379956515522315877990205067767789263494919745199140967669755099750342879536569623,8753253616510946888167801093227774301222649052487951476468798435573884754745089189926142478776371299673097164265750888018064926504126219552267343379956515522315877990205067767789263494919745199140967669755099750342879536569624⟩,
  ⟨1308983285920068397393982281131055398771073270071400848245791556901506426069069546833399607283682191741963811231375034757211277898133384989254096840087614870265276394875110787758289861201070393178727714274488119528399240501392,1308983285920068397393982281131055398771073270071400848245791556901506426069069546833399607283682191741963811231375034757211277898133384989254096840087614870265276394875110787758289861201070393178727714274488119528399240501393⟩,
  ⟨181548963898004824347184022674353837358691980347898252845278782367458350468787035050319992152398812141367941184771129529263568846011506775898878233065764766388773765722771775924518057672409530056257107224550217044148612610332,181548963898004824347184022674353837358691980347898252845278782367458350468787035050319992152398812141367941184771129529263568846011506775898878233065764766388773765722771775924518057672409530056257107224550217044148612610333⟩,
  ⟨23486542211484480814485328010724678207614951018027527181443628413304541137602922491029897259874680473839063598649073590141350679990431548850252933733629453413850653018094093081787497509588583609666167122149906450868407425264,23486542211484480814485328010724678207614951018027527181443628413304541137602922491029897259874680473839063598649073590141350679990431548850252933733629453413850653018094093081787497509588583609666167122149906450868407425265⟩,
  ⟨2847826884674585479955827806656530782097129103496443181886725997920915301471169177259921445527824504178320646035625561243350099545278537661158874244168859080608215932906223936070871492900541647941287956463532816378801766436,2847826884674585479955827806656530782097129103496443181886725997920915301471169177259921445527824504178320646035625561243350099545278537661158874244168859080608215932906223936070871492900541647941287956463532816378801766437⟩,
  ⟨325007096129618375129223098235506332543308235495700416837233767217075457337606579037450755732901561298546260624366504706880717590425182198171998269004233380574245910710296770362545753083439903430463851100161505628622650573,325007096129618375129223098235506332543308235495700416837233767217075457337606579037450755732901561298546260624366504706880717590425182198171998269004233380574245910710296770362545753083439903430463851100161505628622650574⟩,
  ⟨35038198170979178837460629200148704085952374479108665259030121642225888876610420499438541366712810030902099541108175052891525489962415364252125588786766550547469505668019159842293702578407210979455354214862331301994826928,35038198170979178837460629200148704085952374479108665259030121642225888876610420499438541366712810030902099541108175052891525489962415364252125588786766550547469505668019159842293702578407210979455354214862331301994826929⟩,
  ⟨3579788305195796595626225429840359604824844332996120533279676276593874602559144928528443106623263573723118232964036863438106454619175919863923459194829237235310534668693123847471518439759627921842790244001778902576133542,3579788305195796595626225429840359604824844332996120533279676276593874602559144928528443106623263573723118232964036863438106454619175919863923459194829237235310534668693123847471518439759627921842790244001778902576133543⟩,
  ⟨347601172331142647197030051588776826249527524594331996617362317879225088061611314478556958003103274116092257352263641397733387797246184169167912587170303080828070492738285315895770858912769950193009466417285032757885187,347601172331142647197030051588776826249527524594331996617362317879225088061611314478556958003103274116092257352263641397733387797246184169167912587170303080828070492738285315895770858912769950193009466417285032757885188⟩,
  ⟨32160664987855284923273041294822482011260633579858195165293348367260477712830820748276922027417555100828014071548566473668549966632168691825622521108626302434875391675959615314182625555059758870031484545042719552555638,32160664987855284923273041294822482011260633579858195165293348367260477712830820748276922027417555100828014071548566473668549966632168691825622521108626302434875391675959615314182625555059758870031484545042719552555639⟩,
  ⟨2841778443435577197448777827927569742656858246404795215749524709529153451265495696220086613180331486642151490802601304626582880542332237726382042704476650976669472627366137848274603826117034152451210799398093913293747,2841778443435577197448777827927569742656858246404795215749524709529153451265495696220086613180331486642151490802601304626582880542332237726382042704476650976669472627366137848274603826117034152451210799398093913293748⟩,
  ⟨240316859883259114111526949246561756419426436756575207537929503718970431252472019886409748742886214203718103848478566892260119958589954487325964257796752747239159846831407131977323062952038484084055927399604467091871,240316859883259114111526949246561756419426436756575207537929503718970431252472019886409748742886214203718103848478566892260119958589954487325964257796752747239159846831407131977323062952038484084055927399604467091872⟩,
  ⟨19486480754986815068220190820074763949647027975347167193711026579628480808677684774080593918950844479831895936932123231725139752290278201552334007116411320982876383730510659531025854807659662759665445481586929691157,19486480754986815068220190820074763949647027975347167193711026579628480808677684774080593918950844479831895936932123231725139752290278201552334007116411320982876383730510659531025854807659662759665445481586929691158⟩,
  ⟨1517726789713648567080503658245306027658370827059335654527785169375839530456435644097573252133928345356309863890858702111027661731653116630832160274073214268278134690106145837926759270885679449817203027659495181835,1517726789713648567080503658245306027658370827059335654527785169375839530456435644097573252133928345356309863890858702111027661731653116630832160274073214268278134690106145837926759270885679449817203027659495181836⟩,
  ⟨113725813609350660330802460453859452904786246320769101467224846480435578232462357828528718718905040735270324211051673181785327398327100615120243363642355633121164080133171076948747974186116999270774765998038197973,113725813609350660330802460453859452904786246320769101467224846480435578232462357828528718718905040735270324211051673181785327398327100615120243363642355633121164080133171076948747974186116999270774765998038197974⟩,
  ⟨8210503570881288581681746898942749498452416816389914380334642270716823747209729992112698418676831361374547450421395503305499272040599909643852600160283868011121946830868751277103285977542245070139146813625800422,8210503570881288581681746898942749498452416816389914380334642270716823747209729992112698418676831361374547450421395503305499272040599909643852600160283868011121946830868751277103285977542245070139146813625800423⟩,
  ⟨571897051196447286146276740788086329262574514544097493010469773967707649157497489080244993557712130134261687842932264563575640652506971484081683581534834361959876839750141909943416536855473415873148966944157604,571897051196447286146276740788086329262574514544097493010469773967707649157497489080244993557712130134261687842932264563575640652506971484081683581534834361959876839750141909943416536855473415873148966944157605⟩,
  ⟨38481552089787049514144753142519553204867892957625457297730040541541476956619340569093859255212623754321111282783106197310622850776145031058056631054259745021824074035586874672484087813935370833783475974973448,38481552089787049514144753142519553204867892957625457297730040541541476956619340569093859255212623754321111282783106197310622850776145031058056631054259745021824074035586874672484087813935370833783475974973449⟩,
  ⟨2504293028155512857157831298152472613907055238114570834960457337473541012220832677332849190881822201726441488145959412772919167942666639107057437957385057781170092715297658341600130799250357973462920596748610,2504293028155512857157831298152472613907055238114570834960457337473541012220832677332849190881822201726441488145959412772919167942666639107057437957385057781170092715297658341600130799250357973462920596748611⟩,
  ⟨157794724177698218907207321087051077956468873238940367226141700633304998102539624026707623930104674124861699704533901073628215393394245497724835391889160330115945277130051999318387132570369906858106845929123,157794724177698218907207321087051077956468873238940367226141700633304998102539624026707623930104674124861699704533901073628215393394245497724835391889160330115945277130051999318387132570369906858106845929124⟩,
  ⟨9636529208871622345965680800971515589829938386203254776182616017214203029228793371170174856688108520351867198252850073200266158509539736823693844953862656204598721367186756485233788549303926785812104268392,9636529208871622345965680800971515589829938386203254776182616017214203029228793371170174856688108520351867198252850073200266158509539736823693844953862656204598721367186756485233788549303926785812104268393⟩,
  ⟨570936450618282026636460895331690759559615461530073144944101323490934152446007082164503216895285811755982247711158240823390286495478329195210741508946032662006051657835833120717808823509917978873693976828,570936450618282026636460895331690759559615461530073144944101323490934152446007082164503216895285811755982247711158240823390286495478329195210741508946032662006051657835833120717808823509917978873693976829⟩,
  ⟨32846315097908286693015854359201155895159689737434652871198891687747659447997892192459743872420620520497592455197684460030982394919734441303818619391612061248757546514721776491022437160534687791239252644,32846315097908286693015854359201155895159689737434652871198891687747659447997892192459743872420620520497592455197684460030982394919734441303818619391612061248757546514721776491022437160534687791239252645⟩,
  ⟨1836483390464099892682302300947447530979371487322172601143603191083787826083103379814135887449223730489787581094617997318138041295996831342006796508878884585075986400538016655190084442868038715244857015,1836483390464099892682302300947447530979371487322172601143603191083787826083103379814135887449223730489787581094617997318138041295996831342006796508878884585075986400538016655190084442868038715244857016⟩,
  ⟨99870552662558979809845503119192703735282840417875633729996630131665180754047645179776248260738373204215652735398364912256365389958652017477826883285306942986087134673140536628108761636760875040930160,99870552662558979809845503119192703735282840417875633729996630131665180754047645179776248260738373204215652735398364912256365389958652017477826883285306942986087134673140536628108761636760875040930161⟩,
  ⟨5286488928865421560605686010429498474830726652734304760751026418493029102195886338594392798507898862420518963745350752773260787174845976555354687114678393406294899974318793810404413147089697939398584,5286488928865421560605686010429498474830726652734304760751026418493029102195886338594392798507898862420518963745350752773260787174845976555354687114678393406294899974318793810404413147089697939398585⟩,
  ⟨272576384484467516539117224630418928531261074185109105921128488472547358231258386614342988860738216028168843205138107208629022826864093705678188721169407730623523027909167592607062626028651386307214,272576384484467516539117224630418928531261074185109105921128488472547358231258386614342988860738216028168843205138107208629022826864093705678188721169407730623523027909167592607062626028651386307215⟩,
  ⟨13699207191079829957715731189817305017833776708082251539487709655895557141902961276091782002777943895973437846250410588581871807296943062170022112788867597531262531494912488943905123769866991337976,13699207191079829957715731189817305017833776708082251539487709655895557141902961276091782002777943895973437846250410588581871807296943062170022112788867597531262531494912488943905123769866991337977⟩,
  ⟨671535808042541307068532211457055749029960764190956161421848949180949392045475207229226383002557812338430261653456780509063865057561206468780952749863039494021983315863926071956301123500003415391,671535808042541307068532211457055749029960764190956161421848949180949392045475207229226383002557812338430261653456780509063865057561206468780952749863039494021983315863926071956301123500003415392⟩,
  ⟨32127412831933249150084082870442414170237943373737870048276624961631222240413065197755644908559742584579491016517479429821635584108374977776113635026087315817632706494575263646509942775034843120,32127412831933249150084082870442414170237943373737870048276624961631222240413065197755644908559742584579491016517479429821635584108374977776113635026087315817632706494575263646509942775034843121⟩,
  ⟨1500958114937296306576464950305802855582904161354912393151916122909896996748973375745170990692748023959026714355020210812659375893649655243935927598012221741733984315166031345972255185301481743,1500958114937296306576464950305802855582904161354912393151916122909896996748973375745170990692748023959026714355020210812659375893649655243935927598012221741733984315166031345972255185301481744⟩,
  ⟨68515535970496935647156453078858493742014162826500442001482659988600037511172038064945332096814409122497550647733552322686620548363840898892669062447143509406249386463658004106528172361578051,68515535970496935647156453078858493742014162826500442001482659988600037511172038064945332096814409122497550647733552322686620548363840898892669062447143509406249386463658004106528172361578052⟩,
  ⟨3057507271168566550433539713585894705817026995352599319383532842964604993377538357999422388448190419175795158871337466470232062005582631052462074736691562807235893975338212001054593895984499,3057507271168566550433539713585894705817026995352599319383532842964604993377538357999422388448190419175795158871337466470232062005582631052462074736691562807235893975338212001054593895984500⟩,
  ⟨133451603379243928587531776074994360957891112913304040083395143570757750470826572290888391125009128942038642593027457074508101572332020708990850209280907997631580599946528023234305094737637,133451603379243928587531776074994360957891112913304040083395143570757750470826572290888391125009128942038642593027457074508101572332020708990850209280907997631580599946528023234305094737638⟩,
  ⟨5699912238044744126441451948326288002738935837334126390745390507654380129498146482997910025070588015484765037814854040836096245278897711384529095760397644949659619974288054794265909593324,5699912238044744126441451948326288002738935837334126390745390507654380129498146482997910025070588015484765037814854040836096245278897711384529095760397644949659619974288054794265909593325⟩,
  ⟨238342656894074503861300861663046624297799145269998855598098941625840335618211312421027298330879657253222989887227940511547377029168755636212568773225515879642965807778036825201867284263,238342656894074503861300861663046624297799145269998855598098941625840335618211312421027298330879657253222989887227940511547377029168755636212568773225515879642965807778036825201867284264⟩,
  ⟨9761516605756661840630430052792272874677783651778152802760765818731634301980556271724692493341951789041983795315862493225796338425399248838925238921759917139419928598752198877007409036,9761516605756661840630430052792272874677783651778152802760765818731634301980556271724692493341951789041983795315862493225796338425399248838925238921759917139419928598752198877007409037⟩,
  ⟨391741389947493524166163261098173068028248490338949901024967652483561474055928027123868767067944761606974473944626216689838875452554097314026528130416780816855524514251532224231161322,391741389947493524166163261098173068028248490338949901024967652483561474055928027123868767067944761606974473944626216689838875452554097314026528130416780816855524514251532224231161323⟩,
  ⟨15410812108485147044031495773408280247983618533955594712451084302250693539800695070766146464181667438732568904227625419509640267792932412678673295636007573394303824632553754028934054,15410812108485147044031495773408280247983618533955594712451084302250693539800695070766146464181667438732568904227625419509640267792932412678673295636007573394303824632553754028934055⟩
]
def z2Table : List Box := [
  ⟨552006432818029843608526040342223130758003917197047683960551835742595894288489559584312323139074303271284526470091048251083228460129711783624635475570197738383806213696302188640094323780123891493426844157765855555873012214690153904,552006432818029843608526040342223130758003917197047683960551835742595894288489559584312323139074303271284526470091048251083228460129711783624635475570197738383806213696302188640094323780123891493426844157765855555873012214690153905⟩,
  ⟨525720412207647470103358133659260124531432302092426365676716034040567518369990056746964117275308860258366215685800998334364979485837820746309176643400188322270291632091716370133423165504879896660406518245491291005593344966371575147,525720412207647470103358133659260124531432302092426365676716034040567518369990056746964117275308860258366215685800998334364979485837820746309176643400188322270291632091716370133423165504879896660406518245491291005593344966371575148⟩,
  ⟨283889022592129633855813392176000467246973443129910237465426658381906459919794630643360623328666784539517756470332539100557088922352423203006955387436101694025957481329526839872048509372635144196619519852565297143020406281840650579,283889022592129633855813392176000467246973443129910237465426658381906459919794630643360623328666784539517756470332539100557088922352423203006955387436101694025957481329526839872048509372635144196619519852565297143020406281840650580⟩,
  ⟨111516451074349463355257785927721844597576548928696501810212492069211291775452436279659055179610970357835257872745666313350147163662568037095885954660646007754304285595212563361635216925277553837055928112679970819368285295897000788,111516451074349463355257785927721844597576548928696501810212492069211291775452436279659055179610970357835257872745666313350147163662568037095885954660646007754304285595212563361635216925277553837055928112679970819368285295897000789⟩,
  ⟨35048027480509831340223875577284008302095486806161757711781068936037834557999337116464274485020590683891081045720066555624331965722521383087278442893345888151352775472781091342228211033658659777360434549699419400372889664424771676,35048027480509831340223875577284008302095486806161757711781068936037834557999337116464274485020590683891081045720066555624331965722521383087278442893345888151352775472781091342228211033658659777360434549699419400372889664424771677⟩,
  ⟨9264443627715186186436800677072276320414051757153247842694576264211399624422202398617829199536911383574006038658870739878319918211967190774119756233345976028819125264833043725428156483023058318770800181668797575762903701505289296,9264443627715186186436800677072276320414051757153247842694576264211399624422202398617829199536911383574006038658870739878319918211967190774119756233345976028819125264833043725428156483023058318770800181668797575762903701505289297⟩,
  ⟨2124122877606656444862053065289939897096696170070409558289761753699262700484808310088743908183066102054004911861822215492383755498334629278016875326869447766748653058956429778316861274767191501658208154527237539416538767540895253,2124122877606656444862053065289939897096696170070409558289761753699262700484808310088743908183066102054004911861822215492383755498334629278016875326869447766748653058956429778316861274767191501658208154527237539416538767540895254⟩,
  ⟨431360338221659462648909237874264717564252145306606248760382386905081040713837995279560301354099577647890228255016203761530239578123340099535734681764257084939726467357305739596654905029645043413666886765531315696897103562151036,431360338221659462648909237874264717564252145306606248760382386905081040713837995279560301354099577647890228255016203761530239578123340099535734681764257084939726467357305739596654905029645043413666886765531315696897103562151037⟩,
  ⟨78779282548598521993510209839049968711003841472391563288219185920164962792705802709335282308987341697057874478391757992162584338537135975970406090419608639700842901911845609910103371454277706792268709027795897753085915829126609,78779282548598521993510209839049968711003841472391563288219185920164962792705802709335282308987341697057874478391757992162584338537135975970406090419608639700842901911845609910103371454277706792268709027795897753085915829126610⟩,
  ⟨13089832859200683973939822811310553987710732700714008482457915569015064260690695468333996072836821917419638112313750347572112778981333849892540968400876148702652763948751107877582898612010703931787277142744881195283992405013920,13089832859200683973939822811310553987710732700714008482457915569015064260690695468333996072836821917419638112313750347572112778981333849892540968400876148702652763948751107877582898612010703931787277142744881195283992405013921⟩,
  ⟨1997038602878053067819024249417892210945611783826880781298066606042041855156657385553519913676386933555047353032482424821899257306126574534887660563723412430276511422950489535169698634396504830618828179470052387485634738713662,1997038602878053067819024249417892210945611783826880781298066606042041855156657385553519913676386933555047353032482424821899257306126574534887660563723412430276511422950489535169698634396504830618828179470052387485634738713663⟩,
  ⟨281838506537813769773823936128696138491379412216330326177323540959654493651235069892358767118496165686068763183788883081696208159885178586203035204803553440966207836217129116981449970115063003315994005465798877410420889103170,281838506537813769773823936128696138491379412216330326177323540959654493651235069892358767118496165686068763183788883081696208159885178586203035204803553440966207836217129116981449970115063003315994005465798877410420889103171⟩,
  ⟨37021749500769611239425761486534900167262678345453761364527437972971898919125199304378978791861718554318168398463132296163551294088620989595065365174195168047906807127780911168921329407707041423236743434025926612924422963675,37021749500769611239425761486534900167262678345453761364527437972971898919125199304378978791861718554318168398463132296163551294088620989595065365174195168047906807127780911168921329407707041423236743434025926612924422963676⟩,
  ⟨4550099345814657251809123375297088655606315296939805835721272741039056402726492106524310580260621858179647648741131065896330046265952550774407975766059267328039442749944154785075640543168158648026493915402261078800717108028,4550099345814657251809123375297088655606315296939805835721272741039056402726492106524310580260621858179647648741131065896330046265952550774407975766059267328039442749944154785075640543168158648026493915402261078800717108029⟩,
  ⟨525572972564687682561909438002230561289285617186629978885451824633388333149156307491578120500692150463531493116622625793372882349436230463781883831801498258212042585020287397634405538676108164691830313222934969529922403921,525572972564687682561909438002230561289285617186629978885451824633388333149156307491578120500692150463531493116622625793372882349436230463781883831801498258212042585020287397634405538676108164691830313222934969529922403922⟩,
  ⟨57276612883132745530019606877445753677197509327937928532474820425501993640946318856455089705972217179569891727424589815009703273906814717822775347117267795764968554699089981559544295036154046749484643904028462441218136680,57276612883132745530019606877445753677197509327937928532474820425501993640946318856455089705972217179569891727424589815009703273906814717822775347117267795764968554699089981559544295036154046749484643904028462441218136681⟩,
  ⟨5909219929629425002349510877009206046241967918103643942495159403946826497047392346135468286052755659973568374988481903761467592553185130875854513981895152374077198376550850370228104601517089153281160929093845556884048192,5909219929629425002349510877009206046241967918103643942495159403946826497047392346135468286052755659973568374988481903761467592553185130875854513981895152374077198376550850370228104601517089153281160929093845556884048193⟩,
  ⟨578891969781395128618914743306804676202691404437447512975280270610688598830954773468984596493515991814904253287874196526033899399379036452861205379955273443827757050167273075655287259991075659660566721810768951946001488,578891969781395128618914743306804676202691404437447512975280270610688598830954773468984596493515991814904253287874196526033899399379036452861205379955273443827757050167273075655287259991075659660566721810768951946001489⟩,
  ⟨53993790425275966751526778730623825110480306681691109099240969481053915574044418228181645650426298246200878325249424787905074730304312516801258811385056368556719979919956619117217472696223648896573005188563784352581199,53993790425275966751526778730623825110480306681691109099240969481053915574044418228181645650426298246200878325249424787905074730304312516801258811385056368556719979919956619117217472696223648896573005188563784352581200⟩,
  ⟨4806337197665182282230538984931235128388528735131504150758590074379408625049440397728194974857724284074362076969571337845202399171799089746519285155935054944783196936628142639546461259040769681681118547992089341837424,4806337197665182282230538984931235128388528735131504150758590074379408625049440397728194974857724284074362076969571337845202399171799089746519285155935054944783196936628142639546461259040769681681118547992089341837425⟩,
  ⟨409216095854723116432624007221570042942587587482290511067931558172198096982231380255692472297967734076469814675574587866227934798095842232599014149444637740640404058340723850151542950960852917952974355113325523514299,409216095854723116432624007221570042942587587482290511067931558172198096982231380255692472297967734076469814675574587866227934798095842232599014149444637740640404058340723850151542950960852917952974355113325523514300⟩,
  ⟨33389989373700268475771080481396732608484158195305384399611273726268469670041584170146611546946423597838817005598891446442608558096368565878307526029610713902118963182335208434388703959484947895978466608508894000386,33389989373700268475771080481396732608484158195305384399611273726268469670041584170146611546946423597838817005598891446442608558096368565878307526029610713902118963182335208434388703959484947895978466608508894000387⟩,
  ⟨2615693713015065187608456590438767416810083665377689333746171469050018299346634230056160530534815936911217456854188483181062530161523314147765597363774179561786773843062934769821203406280690983227819617954878553380,2615693713015065187608456590438767416810083665377689333746171469050018299346634230056160530534815936911217456854188483181062530161523314147765597363774179561786773843062934769821203406280690983227819617954878553381⟩,
  ⟨197052085701150925960361925574625987962858003593357945128031414497203769933033519810704762048243952672989138810113492079331982528974397831452462403846812832266926723940850030650478863461013881683339523527019210144,197052085701150925960361925574625987962858003593357945128031414497203769933033519810704762048243952672989138810113492079331982528974397831452462403846812832266926723940850030650478863461013881683339523527019210145⟩,
  ⟨14297426279911182153656918519702158231564362863602437325261744349192691228937437227006124838942803253356542196073306614089391016312674287102042089538370859048996920993753547748585413421386835396828724173603940118,14297426279911182153656918519702158231564362863602437325261744349192691228937437227006124838942803253356542196073306614089391016312674287102042089538370859048996920993753547748585413421386835396828724173603940119⟩,
  ⟨1000520354334463287367763581705508383326565216898261889740981054080078400872102854796440340635528217612348893352360761130076194120179770807509472407410753370567425924925258741484586283162319641678370375349309659,1000520354334463287367763581705508383326565216898261889740981054080078400872102854796440340635528217612348893352360761130076194120179770807509472407410753370567425924925258741484586283162319641678370375349309660⟩,
  ⟨67615911760198847143261445050116760575490491429093412543932348111785607329962482287986928153809199446613920179940904144868817534451999255890550824849396560091592503313036775223203531579759665283498856112212474,67615911760198847143261445050116760575490491429093412543932348111785607329962482287986928153809199446613920179940904144868817534451999255890550824849396560091592503313036775223203531579759665283498856112212475⟩,
  ⟨4418252276975550129401804990437430182781128450690330282331967617732539946871109472747813470042930875496127591726949230061590031015038873936295390972896489243246467759641455980914839711970357392026991686015470,4418252276975550129401804990437430182781128450690330282331967617732539946871109472747813470042930875496127591726949230061590031015038873936295390972896489243246467759641455980914839711970357392026991686015471⟩,
  ⟨279459347057277048033004743228173952105068213199894388509295864499211887847635007763935070843955147090204148749332652122807718596776652367887121503662017029933362919648415938071779867929813876788551023783394,279459347057277048033004743228173952105068213199894388509295864499211887847635007763935070843955147090204148749332652122807718596776652367887121503662017029933362919648415938071779867929813876788551023783395⟩,
  ⟨17128093518548460799093826859950722786788463845902194348323039704728024573380212464935096506858574352679467431334747224701708594864349875856322245268380979860181549735074993621534264705297539366210819304844,17128093518548460799093826859950722786788463845902194348323039704728024573380212464935096506858574352679467431334747224701708594864349875856322245268380979860181549735074993621534264705297539366210819304845⟩,
  ⟨1018235768035156887483491485135235832749950381860474239007165642320177442887934657966252060045039236135425366111128218260960454242511767680418377201139973898711483941956375071221695551976575321528416831968,1018235768035156887483491485135235832749950381860474239007165642320177442887934657966252060045039236135425366111128218260960454242511767680418377201139973898711483941956375071221695551976575321528416831969⟩,
  ⟨58767468494851196565833673630318320991339887594309523236595302114681210434659308154052348398375159375673202595027775914180417321471898602944217488284124306722431564817216532966082702171777238887835424505,58767468494851196565833673630318320991339887594309523236595302114681210434659308154052348398375159375673202595027775914180417321471898602944217488284124306722431564817216532966082702171777238887835424506⟩,
  ⟨3295728237864446333724901602933359223264333733789895913089888794344950964883572290932616192604366315739116540268146042104460057868635516576768287148415129118540875444213637708727589134013108876350695282,3295728237864446333724901602933359223264333733789895913089888794344950964883572290932616192604366315739116540268146042104460057868635516576768287148415129118540875444213637708727589134013108876350695283⟩,
  ⟨179740623581424333060593324354602948144244706192966361865534898228762989474660135512209355149268561322297644767341925594290866763944763202882059361899065375814026599126838989553750047001049729939551882,179740623581424333060593324354602948144244706192966361865534898228762989474660135512209355149268561322297644767341925594290866763944763202882059361899065375814026599126838989553750047001049729939551883⟩,
  ⟨9540173456956363078869102862064662498594137596478818707239497096539157538094043531502004610125837560985909512179833752302015798940243279698736605240929270571823305976820865741247191911002798520752503,9540173456956363078869102862064662498594137596478818707239497096539157538094043531502004610125837560985909512179833752302015798940243279698736605240929270571823305976820865741247191911002798520752504⟩,
  ⟨493171458878873878477766322833422980642015961490961055421557547612240057108506605939304152100005980255043762465014781188947385062689950238120796060399233511125451133816849601980584455715211688167150,493171458878873878477766322833422980642015961490961055421557547612240057108506605939304152100005980255043762465014781188947385062689950238120796060399233511125451133816849601980584455715211688167151⟩,
  ⟨24846824897574028361535691823911062714108548275065377972608411119695127505682582667481376171094639056521919681177900878835363007129764639344895251744932461278813382686965264662383141569500126369467,24846824897574028361535691823911062714108548275065377972608411119695127505682582667481376171094639056521919681177900878835363007129764639344895251744932461278813382686965264662383141569500126369468⟩,
  ⟨1220841687613463467703195149076811738469041848202039061834511748541986445135696477514714506525270218214020658627664218333222152196118249155492318130991318001070042846793860018567377825451324038585,1220841687613463467703195149076811738469041848202039061834511748541986445135696477514714506525270218214020658627664218333222152196118249155492318130991318001070042846793860018567377825451324038586⟩,
  ⟨58537366482554555956482133061926311367733262292841583332924728793485982873209961654061668637017172934402041859845788221693715659852336554513501176322476647927625388291475222492917952226757788005,58537366482554555956482133061926311367733262292841583332924728793485982873209961654061668637017172934402041859845788221693715659852336554513501176322476647927625388291475222492917952226757788006⟩,
  ⟨2740621438819877425886258123154339749680566513060017680059306399544001500446881522597813283872576364899902025909342092907464821934553635955706762497885740376249975458546320164261126894463122063,2740621438819877425886258123154339749680566513060017680059306399544001500446881522597813283872576364899902025909342092907464821934553635955706762497885740376249975458546320164261126894463122064⟩,
  ⟨125357798117911228567775128257021682938498106809456572094724846561548804728479072677976317926375807186207601513724836125279514542228887873150945064204354075096671652988866692043238349735364493,125357798117911228567775128257021682938498106809456572094724846561548804728479072677976317926375807186207601513724836125279514542228887873150945064204354075096671652988866692043238349735364494⟩,
  ⟨5604967341928245000676334595149763160231426742358769683502596029971825519774716036217312427250383415565622988907153197129340266037944869777615708789798135900526385197754176975840813978980782,5604967341928245000676334595149763160231426742358769683502596029971825519774716036217312427250383415565622988907153197129340266037944869777615708789798135900526385197754176975840813978980783⟩,
  ⟨245096226235923997436982433778030384117774241005367434802051791829138345568420298768910131078035284665844896626038723755952138546992601589534751117697098732835363658894386356153434112512962,245096226235923997436982433778030384117774241005367434802051791829138345568420298768910131078035284665844896626038723755952138546992601589534751117697098732835363658894386356153434112512963⟩,
  ⟨10487076903339278169897237913174051469103162391879949646316353431536974767201297746525201126558704919141811555038029382508084589283425247993353026021922698704290495542233620308882160507578,10487076903339278169897237913174051469103162391879949646316353431536974767201297746525201126558704919141811555038029382508084589283425247993353026021922698704290495542233620308882160507579⟩,
  ⟨439268247259049782828369352375652279360500264330016876124234461842923543589125032227611162200387830506889270789213812195160835229142966197751635751479196271273896786943848949465333406649,439268247259049782828369352375652279360500264330016876124234461842923543589125032227611162200387830506889270789213812195160835229142966197751635751479196271273896786943848949465333406650⟩,
  ⟨18020103937584702111643510010515961129299430555591695447148512014243827806572689247697963285125459033920825801452805967732588270817488476445220293999171917575354127655570482314633420837,18020103937584702111643510010515961129299430555591695447148512014243827806572689247697963285125459033920825801452805967732588270817488476445220293999171917575354127655570482314633420838⟩,
  ⟨724308169098801911069480301350189171655230071095912951485200962205782596370632668326008883816538369620430738498698394716953092586267823395897644894892355949532279757730026439359900578,724308169098801911069480301350189171655230071095912951485200962205782596370632668326008883816538369620430738498698394716953092586267823395897644894892355949532279757730026439359900579⟩,
  ⟨28536911846197415478612339329514288663387957278671309558372885382525174482633888123768211331121225306170912430187322673909405359555198042694150896094637090899042523758004787529173721,28536911846197415478612339329514288663387957278671309558372885382525174482633888123768211331121225306170912430187322673909405359555198042694150896094637090899042523758004787529173722⟩
]
def expEnclosure (a : Box) : Box :=
  inflate scale (hornerBoxes scale expTable a) (2*(3:ℚ)^48/((48:ℕ).factorial:ℚ))
def cosEnclosure (a : Box) : Box :=
  inflate scale (hornerBoxes scale cosTable (square scale a))
    (2*(16:ℚ)^128/((128:ℕ).factorial:ℚ))
def sinEnclosure (a : Box) : Box :=
  inflate scale (mul scale a (hornerBoxes scale sinTable (square scale a)))
    (2*(16:ℚ)^128/((128:ℕ).factorial:ℚ))

theorem expEnclosure_eq (a : Box) :
    expEnclosure a = GoldbachInterval.Integer.expEnclosure scale 48 3 a := by
  simp only [expEnclosure, GoldbachInterval.Integer.expEnclosure,
    GoldbachInterval.Integer.expPolynomial, expTable_correct, hornerBoxes_map]
theorem cosEnclosure_eq (a : Box) :
    cosEnclosure a = GoldbachInterval.Integer.cosEnclosure scale 64 16 a := by
  simp only [cosEnclosure, GoldbachInterval.Integer.cosEnclosure,
    GoldbachInterval.Integer.cosPolynomial, cosTable_correct, hornerBoxes_map]
theorem sinEnclosure_eq (a : Box) :
    sinEnclosure a = GoldbachInterval.Integer.sinEnclosure scale 64 16 a := by
  simp only [sinEnclosure, GoldbachInterval.Integer.sinEnclosure,
    GoldbachInterval.Integer.sinPolynomial, sinTable_correct, hornerBoxes_map]

def normalizer0 (a : Box) : Box :=
  inflate scale (hornerBoxes scale z0Table (neg a)) (GoldbachInterval.normalizerBudget 0)
def normalizer1 (a : Box) : Box :=
  inflate scale (hornerBoxes scale z1Table (neg a)) (GoldbachInterval.normalizerBudget 1)
def normalizer2 (a : Box) : Box :=
  inflate scale (hornerBoxes scale z2Table (neg a)) (GoldbachInterval.normalizerBudget 2)
end GoldbachInterval.Integer.Cached

-- Dependency: Verification.Check_GoldbachIntegerNegativeChecker

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace GoldbachInterval.Integer

def negativeZBox (b : Rectangle) : ComplexBox := ⟨neg ⟨b.rlo,b.rhi⟩,⟨b.tlo,b.thi⟩⟩
def negativeExpBox (S : ℕ) (b : Rectangle) : Box :=
  endpointEnvelope (expEnclosure S 48 3 (grid (2*b.rlo)))
    (expEnclosure S 48 3 (grid (2*b.rhi)))
def negativeTransformBox (S : ℕ) (b : Rectangle) : ComplexBox :=
  transformEnclosure S (negativeZBox b) (negativeExpBox S b)
    (rectangleCosBox S b) (rectangleSinBox S b)
def negativeLeafCheck (S : ℕ) (b : Rectangle) : Bool :=
  decide (|2*b.rlo| ≤ 3*(S:ℤ) ∧ |2*b.rhi| ≤ 3*(S:ℤ) ∧ |b.tlo+b.thi| ≤ 16*(S:ℤ) ∧
    0 < (squaredNorm S (negativeZBox b)).lo ∧ (negativeTransformBox S b).re.hi ≤ 0)

theorem lift_negativeZBox (S : ℕ) (b : Rectangle) :
    liftComplex S (negativeZBox b) = GoldbachInterval.negativeZBox (liftRectangle S b) := by
  simp only [liftComplex,negativeZBox,GoldbachInterval.negativeZBox,lift_neg]
  rfl

theorem lift_negativeExpBox (S : ℕ) (hS : 0 < S) (b : Rectangle) :
    lift S (negativeExpBox S b) = GoldbachInterval.negativeExpBox S (liftRectangle S b) := by
  have h (n : ℤ) : (((2*n:ℤ):ℚ)/(S:ℚ)) = 2*((n:ℚ)/(S:ℚ)) := by push_cast; ring
  simp only [negativeExpBox,GoldbachInterval.negativeExpBox,GoldbachInterval.negativeExpLower,
    GoldbachInterval.negativeExpUpper,lift_endpointEnvelope,lift_expEnclosure S 48 hS,
    lift_grid S hS,liftRectangle,h]

theorem lift_negativeTransformBox (S : ℕ) (hS : 0 < S) (b : Rectangle) :
    liftComplex S (negativeTransformBox S b) =
      GoldbachInterval.negativeTransformBox S (liftRectangle S b) := by
  simp only [negativeTransformBox,GoldbachInterval.negativeTransformBox,lift_transformEnclosure S hS,
    lift_negativeZBox,lift_negativeExpBox S hS,lift_rectangleCosBox S hS,lift_rectangleSinBox S hS]

theorem negativeLeafCheck_lift (S : ℕ) (hS : 0 < S) (b : Rectangle)
    (hcheck : negativeLeafCheck S b = true) :
    GoldbachInterval.negativeLeafCheck S (liftRectangle S b) = true := by
  have conditions : |2*b.rlo| ≤ 3*(S:ℤ) ∧ |2*b.rhi| ≤ 3*(S:ℤ) ∧ |b.tlo+b.thi| ≤ 16*(S:ℤ) ∧
      0 < (squaredNorm S (negativeZBox b)).lo ∧ (negativeTransformBox S b).re.hi ≤ 0 :=
    of_decide_eq_true hcheck
  rcases conditions with ⟨hlo,hhi,hc,hd,hh⟩
  have hs : (0:ℚ) < (S:ℚ) := by exact_mod_cast hS
  have bound (n : ℤ) (Q : ℚ) (h : (|n|:ℚ) ≤ Q*(S:ℚ)) : |(n:ℚ)/(S:ℚ)| ≤ Q := by
    rw [abs_div,abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    simpa only [Int.cast_abs] using h
  have htwo (n : ℤ) : 2*((n:ℚ)/(S:ℚ)) = ((2*n:ℤ):ℚ)/(S:ℚ) := by push_cast; ring
  have hsum : (b.tlo:ℚ)/(S:ℚ)+(b.thi:ℚ)/(S:ℚ) = ((b.tlo+b.thi:ℤ):ℚ)/(S:ℚ) := by
    push_cast
    rw [add_div]
  have hden := congrArg GoldbachInterval.Box.lo (lift_squaredNorm S hS (negativeZBox b))
  rw [lift_negativeZBox] at hden
  have hden' : (0:ℚ) < ((squaredNorm S (negativeZBox b)).lo:ℚ)/(S:ℚ) :=
    div_pos (by exact_mod_cast hd) hs
  have htop := congrArg (fun a : GoldbachInterval.ComplexBox => a.re.hi) (lift_negativeTransformBox S hS b)
  have htop' : (((negativeTransformBox S b).re.hi:ℤ):ℚ)/(S:ℚ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hh) hs.le
  simp only [lift] at hden
  simp only [liftComplex,lift] at htop
  simp only [GoldbachInterval.negativeLeafCheck,decide_eq_true_eq]
  refine ⟨?_,?_,?_,?_,?_⟩
  · change |2*((b.rlo:ℚ)/(S:ℚ))| ≤ 3
    rw [htwo]
    exact bound _ 3 (by exact_mod_cast hlo)
  · change |2*((b.rhi:ℚ)/(S:ℚ))| ≤ 3
    rw [htwo]
    exact bound _ 3 (by exact_mod_cast hhi)
  · change |(b.tlo:ℚ)/(S:ℚ)+(b.thi:ℚ)/(S:ℚ)| ≤ 16
    rw [hsum]
    exact bound _ 16 (by exact_mod_cast hc)
  · rw [← hden]
    exact hden'
  · rw [← htop]
    exact htop'

theorem negativeLeafCheck_sound (S : ℕ) (hS : 0 < S) (b : Rectangle)
    (hcheck : negativeLeafCheck S b = true) (r t : ℝ)
    (hrt : GoldbachInterval.InRectangle (liftRectangle S b) r t) :
    (goldbachMiddleG (((-r:ℝ):ℂ)+(t:ℂ)*Complex.I)).re ≤ 0 :=
  GoldbachInterval.negativeLeafCheck_sound S hS (liftRectangle S b)
    (negativeLeafCheck_lift S hS b hcheck) r t hrt


end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachCachedNegativeChecker

set_option autoImplicit false

namespace GoldbachInterval.Integer.Cached

def negativeExpBox (b : Rectangle) : Box :=
  endpointEnvelope (expEnclosure (grid (2*b.rlo))) (expEnclosure (grid (2*b.rhi)))
def negativeCosBox (b : Rectangle) : Box :=
  enlarge (cosEnclosure (grid (b.tlo+b.thi))) (b.thi-b.tlo)
def negativeSinBox (b : Rectangle) : Box :=
  enlarge (sinEnclosure (grid (b.tlo+b.thi))) (b.thi-b.tlo)
def negativeTransformBox (b : Rectangle) : ComplexBox :=
  transformEnclosure scale (negativeZBox b) (negativeExpBox b) (negativeCosBox b) (negativeSinBox b)

theorem negativeExpBox_eq (b : Rectangle) :
    negativeExpBox b = GoldbachInterval.Integer.negativeExpBox scale b := by
  simp only [negativeExpBox, GoldbachInterval.Integer.negativeExpBox, expEnclosure_eq]
theorem negativeCosBox_eq (b : Rectangle) : negativeCosBox b = rectangleCosBox scale b := by
  simp only [negativeCosBox, rectangleCosBox, cosMidpointEnclosure, cosEnclosure_eq]
theorem negativeSinBox_eq (b : Rectangle) : negativeSinBox b = rectangleSinBox scale b := by
  simp only [negativeSinBox, rectangleSinBox, sinMidpointEnclosure, sinEnclosure_eq]
theorem negativeTransformBox_eq (b : Rectangle) :
    negativeTransformBox b = GoldbachInterval.Integer.negativeTransformBox scale b := by
  simp only [negativeTransformBox, GoldbachInterval.Integer.negativeTransformBox,
    negativeExpBox_eq, negativeCosBox_eq, negativeSinBox_eq]

def negativeLeafCheck (b : Rectangle) : Bool :=
  decide (|2*b.rlo| ≤ 3*(scale:ℤ) ∧ |2*b.rhi| ≤ 3*(scale:ℤ) ∧
    |b.tlo+b.thi| ≤ 16*(scale:ℤ) ∧ 0 < (squaredNorm scale (negativeZBox b)).lo ∧
    (negativeTransformBox b).re.hi ≤ 0)

theorem negativeLeafCheck_eq (b : Rectangle) :
    negativeLeafCheck b = GoldbachInterval.Integer.negativeLeafCheck scale b := by
  simp only [negativeLeafCheck, GoldbachInterval.Integer.negativeLeafCheck, negativeTransformBox_eq]

end GoldbachInterval.Integer.Cached

-- Dependency: Verification.Check_GoldbachCachedNegativeCells
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem cached_negative_node_0000000 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_0000001 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_000001 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_0000100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_0000101 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_000011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_00010 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_00011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_00100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_00101 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_00110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_00111 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01000 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_010010 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,7398719033620566019069355374704113739896097425321757287459544868717899071396014848920592417074018371482793091603515270748161436147734662334226681545118128866521230745099362831137983001838086338620393980532555046390973723287717150720⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_010011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7398719033620566019069355374704113739896097425321757287459544868717899071396014848920592417074018371482793091603515270748161436147734662334226681545118128866521230745099362831137983001838086338620393980532555046390973723287717150720,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_010100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_010101 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_010110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_0101110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_0101111 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_0110000 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_0110001 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_0110010 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_0110011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_0110100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01101010 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8162849032174821198087993716681751716311596011871381400754547043683846024671340972661571633919367809849048771556009470841824010700697422542515666688302460208473423428609624894026004197109888698182828112948212370854303796348579741696⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01101011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8162849032174821198087993716681751716311596011871381400754547043683846024671340972661571633919367809849048771556009470841824010700697422542515666688302460208473423428609624894026004197109888698182828112948212370854303796348579741696,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01101100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01101101 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01101110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01101111 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01110000 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01110001 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01110010 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01110011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01110100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01110101 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01110110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01110111 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01111000 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01111001 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01111010 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01111011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01111100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01111101 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_01111110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_011111110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_011111111 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10000000 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10000001 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10000010 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10000011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10000100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10000101 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10000110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10000111 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10001000 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10001001 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_100010100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_100010101 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10001011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10001100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10001101 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10001110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10001111 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10010000 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10010001 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_1001001 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_1001010 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_1001011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_1001100 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10011010 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10011011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_1001110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_1001111 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_101000 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_101001 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_101010 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_101011 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_10111 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_110 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760,11546853311486522705170534945439862754723089752305431045346699532818753960604928092085908165663058179756752497059912356970901126578103932036366886608118784722833133884155071172530098061885013433387893556503266236334765548475256930304⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

theorem cached_negative_node_111 : GoldbachInterval.Integer.negativeLeafCheck (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,11546853311486522705170534945439862754723089752305431045346699532818753960604928092085908165663058179756752497059912356970901126578103932036366886608118784722833133884155071172530098061885013433387893556503266236334765548475256930304,12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848⟩ = true := by
  rw [show (2^768:ℕ) = GoldbachInterval.Integer.Cached.scale from rfl,
    ← GoldbachInterval.Integer.Cached.negativeLeafCheck_eq]
  decide +kernel

-- Dependency: Verification.Check_GoldbachIntegerGeometry

set_option autoImplicit false

namespace GoldbachInterval.Integer

theorem rectangle_split_R (S : ℕ) (P : ℝ → ℝ → Prop) (box : Rectangle) (middle : ℤ)
    (hl : ∀ r t : ℝ, GoldbachInterval.InRectangle
      (liftRectangle S {box with rhi := middle}) r t → P r t)
    (hr : ∀ r t : ℝ, GoldbachInterval.InRectangle
      (liftRectangle S {box with rlo := middle}) r t → P r t) :
    ∀ r t : ℝ, GoldbachInterval.InRectangle (liftRectangle S box) r t → P r t := by
  intro r t h
  by_cases hm : r ≤ ((liftRectangle S {box with rhi := middle}).rhi:ℝ)
  · exact hl r t ⟨h.1,hm,h.2.2.1,h.2.2.2⟩
  · exact hr r t ⟨le_of_not_ge hm,h.2.1,h.2.2.1,h.2.2.2⟩

theorem rectangle_split_T (S : ℕ) (P : ℝ → ℝ → Prop) (box : Rectangle) (middle : ℤ)
    (hl : ∀ r t : ℝ, GoldbachInterval.InRectangle
      (liftRectangle S {box with thi := middle}) r t → P r t)
    (hr : ∀ r t : ℝ, GoldbachInterval.InRectangle
      (liftRectangle S {box with tlo := middle}) r t → P r t) :
    ∀ r t : ℝ, GoldbachInterval.InRectangle (liftRectangle S box) r t → P r t := by
  intro r t h
  by_cases hm : t ≤ ((liftRectangle S {box with thi := middle}).thi:ℝ)
  · exact hl r t ⟨h.1,h.2.1,h.2.2.1,hm⟩
  · exact hr r t ⟨h.1,h.2.1,le_of_not_ge hm,h.2.2.2⟩


end GoldbachInterval.Integer

-- Dependency: Verification.Check_GoldbachCachedNegativeMiddleCertificate
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option exponentiation.threshold 1024
noncomputable def cachedNegativePredicate (b t : ℝ) : Prop :=
  (goldbachMiddleG (((-b:ℝ):ℂ)+(t:ℂ)*Complex.I)).re ≤ 0

def cachedNegativeRoot : GoldbachInterval.Rectangle :=
  GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848⟩

theorem cached_negative_node_0000000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩ cached_negative_node_0000000

theorem cached_negative_node_0000001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩ cached_negative_node_0000001

theorem cached_negative_node_000000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩ (931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713)
    cached_negative_node_0000000_sound cached_negative_node_0000001_sound

theorem cached_negative_node_000001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩ cached_negative_node_000001

theorem cached_negative_node_00000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩ (5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632)
    cached_negative_node_000000_sound cached_negative_node_000001_sound

theorem cached_negative_node_0000100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩ cached_negative_node_0000100

theorem cached_negative_node_0000101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩ cached_negative_node_0000101

theorem cached_negative_node_000010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632⟩ (1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285)
    cached_negative_node_0000100_sound cached_negative_node_0000101_sound

theorem cached_negative_node_000011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩ cached_negative_node_000011

theorem cached_negative_node_00001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩ (5652136179782268467026753450183798365232100656065473599928111325938591749623840851798354207141791083788494394569242813391218408598105496143851858360696800084916218897075906687393934555502538088191973106439624019046219270577174085632)
    cached_negative_node_000010_sound cached_negative_node_000011_sound

theorem cached_negative_node_0000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_00000_sound cached_negative_node_00001_sound

theorem cached_negative_node_00010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040⟩ cached_negative_node_00010

theorem cached_negative_node_00011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040⟩ cached_negative_node_00011

theorem cached_negative_node_0001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_00010_sound cached_negative_node_00011_sound

theorem cached_negative_node_000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040⟩ (5870459036512055661032078690748837787065100252222509060869540518786005164845362601438633983383319494750281731698526870560836287041809141917648711258749466182616845378078838705361940611294481619495525715701240397464313577165991968768)
    cached_negative_node_0000_sound cached_negative_node_0001_sound

theorem cached_negative_node_00100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312⟩ cached_negative_node_00100

theorem cached_negative_node_00101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312⟩ cached_negative_node_00101

theorem cached_negative_node_0010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_00100_sound cached_negative_node_00101_sound

theorem cached_negative_node_00110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩ cached_negative_node_00110

theorem cached_negative_node_00111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩ cached_negative_node_00111

theorem cached_negative_node_0011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_00110_sound cached_negative_node_00111_sound

theorem cached_negative_node_001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩ (6743750463431204437053379653008995474397098636850650904635257290175658825731449599999753088349433138597431080215663099239307800816623725012836122850960130573419351302090566777233964834462255744709736152747705911136690803521263501312)
    cached_negative_node_0010_sound cached_negative_node_0011_sound

theorem cached_negative_node_00_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584⟩ (6307104749971630049042729171878916630731099444536579982752398904480831995288406100719193535866376316673856405957094984900072043929216433465242417054854798378018098340084702741297952722878368682102630934224473154300502190343627735040)
    cached_negative_node_000_sound cached_negative_node_001_sound

theorem cached_negative_node_01000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856⟩ cached_negative_node_01000

theorem cached_negative_node_010010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,7398719033620566019069355374704113739896097425321757287459544868717899071396014848920592417074018371482793091603515270748161436147734662334226681545118128866521230745099362831137983001838086338620393980532555046390973723287717150720⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,7398719033620566019069355374704113739896097425321757287459544868717899071396014848920592417074018371482793091603515270748161436147734662334226681545118128866521230745099362831137983001838086338620393980532555046390973723287717150720⟩ cached_negative_node_010010

theorem cached_negative_node_010011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7398719033620566019069355374704113739896097425321757287459544868717899071396014848920592417074018371482793091603515270748161436147734662334226681545118128866521230745099362831137983001838086338620393980532555046390973723287717150720,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7398719033620566019069355374704113739896097425321757287459544868717899071396014848920592417074018371482793091603515270748161436147734662334226681545118128866521230745099362831137983001838086338620393980532555046390973723287717150720,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856⟩ cached_negative_node_010011

theorem cached_negative_node_01001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856⟩ (7398719033620566019069355374704113739896097425321757287459544868717899071396014848920592417074018371482793091603515270748161436147734662334226681545118128866521230745099362831137983001838086338620393980532555046390973723287717150720)
    cached_negative_node_010010_sound cached_negative_node_010011_sound

theorem cached_negative_node_0100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_01000_sound cached_negative_node_01001_sound

theorem cached_negative_node_010100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992⟩ cached_negative_node_010100

theorem cached_negative_node_010101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ cached_negative_node_010101

theorem cached_negative_node_01010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ (7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992)
    cached_negative_node_010100_sound cached_negative_node_010101_sound

theorem cached_negative_node_010110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992⟩ cached_negative_node_010110

theorem cached_negative_node_0101110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ cached_negative_node_0101110

theorem cached_negative_node_0101111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ cached_negative_node_0101111

theorem cached_negative_node_010111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ (1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285)
    cached_negative_node_0101110_sound cached_negative_node_0101111_sound

theorem cached_negative_node_01011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ (7835364747080140407080005855834192583562096617635828209342403254412725901839058348201151969557075193406367765862083385087397193035141953881820387341223461061922483707105226867073995113421973401227499199055787803227162336465352916992)
    cached_negative_node_010110_sound cached_negative_node_010111_sound

theorem cached_negative_node_0101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_01010_sound cached_negative_node_01011_sound

theorem cached_negative_node_010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128⟩ (7617041890350353213074680615269153161729097021478792748400974061565312486617536598560872193315546782444580428732799327917779314591438308108023534443170794964221857226102294849105989057630029869923946589794171424809068029876535033856)
    cached_negative_node_0100_sound cached_negative_node_0101_sound

theorem cached_negative_node_0110000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ cached_negative_node_0110000

theorem cached_negative_node_0110001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ cached_negative_node_0110001

theorem cached_negative_node_011000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ (931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713)
    cached_negative_node_0110000_sound cached_negative_node_0110001_sound

theorem cached_negative_node_0110010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ cached_negative_node_0110010

theorem cached_negative_node_0110011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ cached_negative_node_0110011

theorem cached_negative_node_011001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ (931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713)
    cached_negative_node_0110010_sound cached_negative_node_0110011_sound

theorem cached_negative_node_01100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ (8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264)
    cached_negative_node_011000_sound cached_negative_node_011001_sound

theorem cached_negative_node_0110100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ cached_negative_node_0110100

theorem cached_negative_node_01101010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8162849032174821198087993716681751716311596011871381400754547043683846024671340972661571633919367809849048771556009470841824010700697422542515666688302460208473423428609624894026004197109888698182828112948212370854303796348579741696⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8162849032174821198087993716681751716311596011871381400754547043683846024671340972661571633919367809849048771556009470841824010700697422542515666688302460208473423428609624894026004197109888698182828112948212370854303796348579741696⟩ cached_negative_node_01101010

theorem cached_negative_node_01101011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8162849032174821198087993716681751716311596011871381400754547043683846024671340972661571633919367809849048771556009470841824010700697422542515666688302460208473423428609624894026004197109888698182828112948212370854303796348579741696,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8162849032174821198087993716681751716311596011871381400754547043683846024671340972661571633919367809849048771556009470841824010700697422542515666688302460208473423428609624894026004197109888698182828112948212370854303796348579741696,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ cached_negative_node_01101011

theorem cached_negative_node_0110101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ (8162849032174821198087993716681751716311596011871381400754547043683846024671340972661571633919367809849048771556009470841824010700697422542515666688302460208473423428609624894026004197109888698182828112948212370854303796348579741696)
    cached_negative_node_01101010_sound cached_negative_node_01101011_sound

theorem cached_negative_node_011010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264⟩ (1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285)
    cached_negative_node_0110100_sound cached_negative_node_0110101_sound

theorem cached_negative_node_01101100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832⟩ cached_negative_node_01101100

theorem cached_negative_node_01101101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ cached_negative_node_01101101

theorem cached_negative_node_0110110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ (8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832)
    cached_negative_node_01101100_sound cached_negative_node_01101101_sound

theorem cached_negative_node_01101110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832⟩ cached_negative_node_01101110

theorem cached_negative_node_01101111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ cached_negative_node_01101111

theorem cached_negative_node_0110111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ (8381171888904608392093318957246791138144595608028416861695976236531259439892862722301851410160896220810836108685293528011441889144401068316312519586355126306174049909612556911994010252901832229486380722209828749272398102937397624832)
    cached_negative_node_01101110_sound cached_negative_node_01101111_sound

theorem cached_negative_node_011011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ (1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285)
    cached_negative_node_0110110_sound cached_negative_node_0110111_sound

theorem cached_negative_node_01101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ (8272010460539714795090656336964271427228095809949899131225261640107552732282101847481711522040132015329942440120651499426632949922549245429414093137328793257323736669111090903010007225005860463834604417579020560063350949642988683264)
    cached_negative_node_011010_sound cached_negative_node_011011_sound

theorem cached_negative_node_0110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_01100_sound cached_negative_node_01101_sound

theorem cached_negative_node_01110000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩ cached_negative_node_01110000

theorem cached_negative_node_01110001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ cached_negative_node_01110001

theorem cached_negative_node_0111000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ (8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968)
    cached_negative_node_01110000_sound cached_negative_node_01110001_sound

theorem cached_negative_node_01110010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩ cached_negative_node_01110010

theorem cached_negative_node_01110011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ cached_negative_node_01110011

theorem cached_negative_node_0111001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ (8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968)
    cached_negative_node_01110010_sound cached_negative_node_01110011_sound

theorem cached_negative_node_011100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ (931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713)
    cached_negative_node_0111000_sound cached_negative_node_0111001_sound

theorem cached_negative_node_01110100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩ cached_negative_node_01110100

theorem cached_negative_node_01110101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ cached_negative_node_01110101

theorem cached_negative_node_0111010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104)
    cached_negative_node_01110100_sound cached_negative_node_01110101_sound

theorem cached_negative_node_01110110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩ cached_negative_node_01110110

theorem cached_negative_node_01110111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ cached_negative_node_01110111

theorem cached_negative_node_0111011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104)
    cached_negative_node_01110110_sound cached_negative_node_01110111_sound

theorem cached_negative_node_011101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713)
    cached_negative_node_0111010_sound cached_negative_node_0111011_sound

theorem cached_negative_node_01110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536)
    cached_negative_node_011100_sound cached_negative_node_011101_sound

theorem cached_negative_node_01111000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩ cached_negative_node_01111000

theorem cached_negative_node_01111001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ cached_negative_node_01111001

theorem cached_negative_node_0111100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ (8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968)
    cached_negative_node_01111000_sound cached_negative_node_01111001_sound

theorem cached_negative_node_01111010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968⟩ cached_negative_node_01111010

theorem cached_negative_node_01111011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ cached_negative_node_01111011

theorem cached_negative_node_0111101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ (8599494745634395586098644197811830559977595204185452322637405429378672855114384471942131186402424631772623445814577585181059767588104714090109372484407792403874676390615488929962016308693775760789933331471445127690492409526215507968)
    cached_negative_node_01111010_sound cached_negative_node_01111011_sound

theorem cached_negative_node_011110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536⟩ (1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285)
    cached_negative_node_0111100_sound cached_negative_node_0111101_sound

theorem cached_negative_node_01111100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩ cached_negative_node_01111100

theorem cached_negative_node_01111101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ cached_negative_node_01111101

theorem cached_negative_node_0111110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104)
    cached_negative_node_01111100_sound cached_negative_node_01111101_sound

theorem cached_negative_node_01111110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104⟩ cached_negative_node_01111110

theorem cached_negative_node_011111110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ cached_negative_node_011111110

theorem cached_negative_node_011111111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ cached_negative_node_011111111

theorem cached_negative_node_01111111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178)
    cached_negative_node_011111110_sound cached_negative_node_011111111_sound

theorem cached_negative_node_0111111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (8817817602364182780103969438376869981810594800342487783578834622226086270335906221582410962643953042734410782943861642350677646031808359863906225382460458501575302871618420947930022364485719292093485940733061506108586716115033391104)
    cached_negative_node_01111110_sound cached_negative_node_01111111_sound

theorem cached_negative_node_011111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285)
    cached_negative_node_0111110_sound cached_negative_node_0111111_sound

theorem cached_negative_node_01111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (8708656173999289183101306818094350270894095002263970053108120025802379562725145346762271074523188837253517114379219613765868706809956536977007798933434125452724989631116954938946019336589747526441709636102253316899539562820624449536)
    cached_negative_node_011110_sound cached_negative_node_011111_sound

theorem cached_negative_node_0111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_01110_sound cached_negative_node_01111_sound

theorem cached_negative_node_011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (8490333317269501989095981577529310849061095406106934592166690832954966147503623597121991298281660426291729777249935556596250828366252891203210946035381459355024363150114022920978013280797803995138157026840636938481445256231806566400)
    cached_negative_node_0110_sound cached_negative_node_0111_sound

theorem cached_negative_node_01_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (8053687603809927601085331096399232005395096213792863670283832447260139317060580097841431745798603604368155102991367442257015071478845599655617240239276127159623110188108158885042001169213916932531051808317404181645256643054170800128)
    cached_negative_node_010_sound cached_negative_node_011_sound

theorem cached_negative_node_0_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672⟩ (7180396176890778825064030134139074318063097829164721826518115675870485656174493099280312640832489960521005754474231213578543557704031016560429828647065462768820604264096430813169976946046142807316841371270938667972879416698899267584)
    cached_negative_node_00_sound cached_negative_node_01_sound

theorem cached_negative_node_10000000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ cached_negative_node_10000000

theorem cached_negative_node_10000001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ cached_negative_node_10000001

theorem cached_negative_node_1000000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ (9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240)
    cached_negative_node_10000000_sound cached_negative_node_10000001_sound

theorem cached_negative_node_10000010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ cached_negative_node_10000010

theorem cached_negative_node_10000011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ cached_negative_node_10000011

theorem cached_negative_node_1000001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ (9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240)
    cached_negative_node_10000010_sound cached_negative_node_10000011_sound

theorem cached_negative_node_100000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ (931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713)
    cached_negative_node_1000000_sound cached_negative_node_1000001_sound

theorem cached_negative_node_10000100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩ cached_negative_node_10000100

theorem cached_negative_node_10000101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ cached_negative_node_10000101

theorem cached_negative_node_1000010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ (9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376)
    cached_negative_node_10000100_sound cached_negative_node_10000101_sound

theorem cached_negative_node_10000110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩ cached_negative_node_10000110

theorem cached_negative_node_10000111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ cached_negative_node_10000111

theorem cached_negative_node_1000011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ (9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376)
    cached_negative_node_10000110_sound cached_negative_node_10000111_sound

theorem cached_negative_node_100001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ (931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713)
    cached_negative_node_1000010_sound cached_negative_node_1000011_sound

theorem cached_negative_node_10000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ (9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808)
    cached_negative_node_100000_sound cached_negative_node_100001_sound

theorem cached_negative_node_10001000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ cached_negative_node_10001000

theorem cached_negative_node_10001001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ cached_negative_node_10001001

theorem cached_negative_node_1000100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ (9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240)
    cached_negative_node_10001000_sound cached_negative_node_10001001_sound

theorem cached_negative_node_100010100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ cached_negative_node_100010100

theorem cached_negative_node_100010101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ cached_negative_node_100010101

theorem cached_negative_node_10001010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240⟩ (1319640378455602594876632565193127171968353114549192119468194232322143309783420353381246647504349506257914571092561412225245843037497592232727644183785003968323786729617722419717725492786858678101473549314658998438258919825743649178)
    cached_negative_node_100010100_sound cached_negative_node_100010101_sound

theorem cached_negative_node_10001011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ cached_negative_node_10001011

theorem cached_negative_node_1000101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ (9036140459093969974109294678941909403643594396499523244520263815073499685557427971222690738885481453696198120073145699520295524475512005637703078280513124599275929352621352965898028420277662823397038549994677884526681022703851274240)
    cached_negative_node_10001010_sound cached_negative_node_10001011_sound

theorem cached_negative_node_100010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808⟩ (1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285)
    cached_negative_node_1000100_sound cached_negative_node_1000101_sound

theorem cached_negative_node_10001100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩ cached_negative_node_10001100

theorem cached_negative_node_10001101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ cached_negative_node_10001101

theorem cached_negative_node_1000110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ (9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376)
    cached_negative_node_10001100_sound cached_negative_node_10001101_sound

theorem cached_negative_node_10001110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376⟩ cached_negative_node_10001110

theorem cached_negative_node_10001111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ cached_negative_node_10001111

theorem cached_negative_node_1000111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ (9254463315823757168114619919506948825476593992656558705461693007920913100778949720862970515127009864657985457202429756689913402919215651411499931178565790696976555833624284983866034476069606354700591159256294262944775329292669157376)
    cached_negative_node_10001110_sound cached_negative_node_10001111_sound

theorem cached_negative_node_100011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ (1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285)
    cached_negative_node_1000110_sound cached_negative_node_1000111_sound

theorem cached_negative_node_10001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ (9145301887458863571111957299224429114560094194578040974990978411497206393168188846042830627006245659177091788637787728105104463697363828524601504729539457648126242593122818974882031448173634589048814854625486073735728175998260215808)
    cached_negative_node_100010_sound cached_negative_node_100011_sound

theorem cached_negative_node_1000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_10000_sound cached_negative_node_10001_sound

theorem cached_negative_node_10010000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512⟩ cached_negative_node_10010000

theorem cached_negative_node_10010001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ cached_negative_node_10010001

theorem cached_negative_node_1001000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ (9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512)
    cached_negative_node_10010000_sound cached_negative_node_10010001_sound

theorem cached_negative_node_1001001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ cached_negative_node_1001001

theorem cached_negative_node_100100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ (931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713)
    cached_negative_node_1001000_sound cached_negative_node_1001001_sound

theorem cached_negative_node_1001010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ cached_negative_node_1001010

theorem cached_negative_node_1001011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ cached_negative_node_1001011

theorem cached_negative_node_100101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ (931510855380425361089387693077501533154131610270017966683431222815630571611826131798527045297187886770292638418278643923702948026468888634866572365024708683522672985612509943330159171378959066895157799516229881250535708112289634713)
    cached_negative_node_1001010_sound cached_negative_node_1001011_sound

theorem cached_negative_node_10010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ (9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080)
    cached_negative_node_100100_sound cached_negative_node_100101_sound

theorem cached_negative_node_1001100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ cached_negative_node_1001100

theorem cached_negative_node_10011010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512⟩ cached_negative_node_10011010

theorem cached_negative_node_10011011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ cached_negative_node_10011011

theorem cached_negative_node_1001101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ (9472786172553544362119945160071988247309593588813594166403122200768326516000471470503250291368538275619772794331713813859531281362919297185296784076618456794677182314627217001834040531861549886004143768517910641362869635881487040512)
    cached_negative_node_10011010_sound cached_negative_node_10011011_sound

theorem cached_negative_node_100110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080⟩ (1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285)
    cached_negative_node_1001100_sound cached_negative_node_1001101_sound

theorem cached_negative_node_1001110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ cached_negative_node_1001110

theorem cached_negative_node_1001111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ cached_negative_node_1001111

theorem cached_negative_node_100111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ (1242014473840567148119183590770002044205508813693357288911241630420840762149101509064702727062917182360390184557704858564937264035291851513155429820032944911363563980816679924440212228505278755860210399354973175000714277483052846285)
    cached_negative_node_1001110_sound cached_negative_node_1001111_sound

theorem cached_negative_node_10011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ (9581947600918437959122607780354507958226093386892111896873836797192033223611232345323390179489302481100666462896355842444340220584771120072195210525644789843527495555128683010818043559757521651655920073148718830571916789175895982080)
    cached_negative_node_100110_sound cached_negative_node_100111_sound

theorem cached_negative_node_1001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_10010_sound cached_negative_node_10011_sound

theorem cached_negative_node_100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216⟩ (9363624744188650765117282539789468536393093790735076435932407604344619808389710595683110403247774070138879125767071785274722342141067474298398357627592123745826869074125750992850037503965578120352367463887102452153822482587078098944)
    cached_negative_node_1000_sound cached_negative_node_1001_sound

theorem cached_negative_node_101000_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352⟩ cached_negative_node_101000

theorem cached_negative_node_101001_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩ cached_negative_node_101001

theorem cached_negative_node_10100_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩ (10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352)
    cached_negative_node_101000_sound cached_negative_node_101001_sound

theorem cached_negative_node_101010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352⟩ cached_negative_node_101010

theorem cached_negative_node_101011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩ cached_negative_node_101011

theorem cached_negative_node_10101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩ (10018593314378012347133258261484586801892092579206182818756695182886860054054275844603949731972359303024241137154923956783575977472178411619788916321750122038928748517134547046754055671341408714263025291671951587408105402353531748352)
    cached_negative_node_101010_sound cached_negative_node_101011_sound

theorem cached_negative_node_1010_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_10100_sound cached_negative_node_10101_sound

theorem cached_negative_node_10110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩ cached_negative_node_10110

theorem cached_negative_node_10111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩ cached_negative_node_10111

theorem cached_negative_node_1011_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_R (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩ (1086762664610496254604285641923751788679820211981687627797336426618235666880463820431614886180052534565341411487991751244320106030880370074011001092528826797443118483214594933885185699942118911377684099435601528125624992797671240499)
    cached_negative_node_10110_sound cached_negative_node_10111_sound

theorem cached_negative_node_101_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩ (10236916171107799541138583502049626223725092175363218279698124375734273469275797594244229508213887713986028474284208013953193855915882057393585769219802788136629374998137479064722061727133352245566577900933567965826199708942349631488)
    cached_negative_node_1010_sound cached_negative_node_1011_sound

theorem cached_negative_node_10_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760⟩ (9800270457648225153127933020919547380059092983049147357815265990039446638832754094963669955730830892062453800025639899613958099028474765845992063423697455941228122036131615028786049615549465182959472682410335208990011095764713865216)
    cached_negative_node_100_sound cached_negative_node_101_sound

theorem cached_negative_node_110_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760,11546853311486522705170534945439862754723089752305431045346699532818753960604928092085908165663058179756752497059912356970901126578103932036366886608118784722833133884155071172530098061885013433387893556503266236334765548475256930304⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760,11546853311486522705170534945439862754723089752305431045346699532818753960604928092085908165663058179756752497059912356970901126578103932036366886608118784722833133884155071172530098061885013433387893556503266236334765548475256930304⟩ cached_negative_node_110

theorem cached_negative_node_111_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,11546853311486522705170534945439862754723089752305431045346699532818753960604928092085908165663058179756752497059912356970901126578103932036366886608118784722833133884155071172530098061885013433387893556503266236334765548475256930304,12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.negativeLeafCheck_sound (2^768) (by norm_num) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,11546853311486522705170534945439862754723089752305431045346699532818753960604928092085908165663058179756752497059912356970901126578103932036366886608118784722833133884155071172530098061885013433387893556503266236334765548475256930304,12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848⟩ cached_negative_node_111

theorem cached_negative_node_11_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760,12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760,12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848⟩ (11546853311486522705170534945439862754723089752305431045346699532818753960604928092085908165663058179756752497059912356970901126578103932036366886608118784722833133884155071172530098061885013433387893556503266236334765548475256930304)
    cached_negative_node_110_sound cached_negative_node_111_sound

theorem cached_negative_node_1_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672,12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848⟩ (10673561884567373929149233983179705067391091367677289201580982761429100299718841093524789060696944535909603148542776128292429612803289348941179475015908120332030627960143343100658073838717239308173683119456800722662388322119985397760)
    cached_negative_node_10_sound cached_negative_node_11_sound

theorem cached_negative_node_root_sound : ∀ b t : ℝ,
    GoldbachInterval.InRectangle (GoldbachInterval.Integer.liftRectangle (2^768) ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848⟩) b t →
      cachedNegativePredicate b t :=
  GoldbachInterval.Integer.rectangle_split_T (2^768) cachedNegativePredicate ⟨776259046150354467574489744231251277628443008558348305569526019013025476343188443165439204414323238975243865348565536603085790022057407195722143637520590569602227488010424952775132642815799222412631499596858234375446423426908028928,1397266283070638041634081539616252299731197415405026950025146834223445857417739197697790567945781830155438957627417965885554422039703332952299858547537063025284009478418764914995238757068438600342736699274344821875803562168434452071,5433813323052481273021428209618758943399101059908438138986682133091178334402319102158074430900262672826707057439958756221600530154401850370055005462644133987215592416072974669425928499710594556888420497178007640628124963988356202496,12420144738405671481191835907700020442055088136933572889112416304208407621491015090647027270629171823603901845577048585649372640352918515131554298200329449113635639808166799244402122285052787558602103993549731750007142774830528462848⟩ (8926979030729076377106632058659389692727094598421005514049549218649792977946667096402550850764717248215304451508503670935486585253660182750804651831486791550425616112119886956914025392381691057745262245363869695317633869409442332672)
    cached_negative_node_0_sound cached_negative_node_1_sound

theorem goldbach_cached_negative_transform_middle_certificate (b t : ℝ)
    (hblo : (1/2:ℝ) ≤ b) (hbhi : b ≤ 9/10)
    (htlo : (7/2:ℝ) ≤ t) (hthi : t ≤ 8) :
    (goldbachMiddleG (((-b:ℝ):ℂ)+(t:ℂ)*Complex.I)).re ≤ 0 := by
  apply cached_negative_node_root_sound b t
  have hpad : (9/10:ℝ) ≤ (cachedNegativeRoot.rhi:ℝ) := by
    norm_num [cachedNegativeRoot, GoldbachInterval.Integer.liftRectangle]
  refine ⟨?_, hbhi.trans hpad, ?_, ?_⟩
  · convert hblo using 1 <;> norm_num [cachedNegativeRoot, GoldbachInterval.Integer.liftRectangle]
  · convert htlo using 1 <;> norm_num [cachedNegativeRoot, GoldbachInterval.Integer.liftRectangle]
  · convert hthi using 1 <;> norm_num [cachedNegativeRoot, GoldbachInterval.Integer.liftRectangle]

-- Dependency: Verification.Check_GoldbachSevenHalvesCachedAdapter

set_option autoImplicit false

-- This is an unconditional statement about the actual defining integral.
theorem goldbach_negative_integral_middle_certificate (b t : ℝ)
    (hblo : (1/2:ℝ) ≤ b) (hbhi : b ≤ 9/10)
    (htlo : (7/2:ℝ) ≤ t) (hthi : t ≤ 8) :
    goldbachMiddleReal (-b) t ≤ 0 := by
  have hz : (((-b:ℝ):ℂ)+(t:ℂ)*Complex.I) ≠ 0 := by
    intro h
    have hi := congrArg Complex.im h
    simp at hi
    linarith
  unfold goldbachMiddleReal
  rw [goldbach_middle_complex_closed_form _ hz]
  exact goldbach_cached_negative_transform_middle_certificate b t hblo hbhi htlo hthi

-- The certificate and analytic tail now cover every absolute frequency at least 7/2.
theorem goldbach_normalized_comparison_from_seven_halves (a b t : ℝ)
    (ha : 0 ≤ a) (hblo : (1/2:ℝ) ≤ b) (hbhi : b ≤ 9/10)
    (ht : (7/2:ℝ) ≤ |t|) :
    goldbachMiddlePhi (-b) t ≤ goldbachMiddlePhi a t := by
  by_cases htail : 8 ≤ |t|
  · simpa only [goldbachMiddlePhi, goldbachMiddleReal, goldbachMiddleZ, neg_neg] using
      GoldbachKernel_normalized_complex_laplace_tail_eight a b t ha hblo (by linarith) htail
  have hn := goldbach_negative_integral_middle_certificate b |t| hblo hbhi ht (by linarith)
  have hp := GoldbachKernel_polynomial_laplace_right_half_plane_nonneg
    ((a:ℂ)+((|t|:ℝ):ℂ)*Complex.I) (by simpa using ha)
  have h : goldbachMiddlePhi (-b) |t| ≤ goldbachMiddlePhi a |t| :=
    (div_nonpos_of_nonpos_of_nonneg hn (laplace_positive (-b)).le).trans
      (div_nonneg hp (laplace_positive a).le)
  have heven (r : ℝ) : goldbachMiddlePhi r |t| = goldbachMiddlePhi r t := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos (le_of_not_ge ht)]
      unfold goldbachMiddlePhi goldbachMiddleReal
      rw [goldbach_polynomial_real_part_even r t]
  rwa [heven (-b),heven a] at h



-- The public statement uses the defining integrals, without local helper definitions.
theorem solution (a b t : ℝ) (ha : 0 ≤ a)
    (hb_lower : (1/2:ℝ) ≤ b) (hb_upper : b ≤ 9/10)
    (ht : (7/2:ℝ) ≤ |t|) :
    ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-(((-b:ℝ):ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
      (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (b*u)) ≤
    ((∫ u in (0:ℝ)..2, ((((2-u)^3*(4+6*u+u^2)/30):ℝ):ℂ)*
      Complex.exp (-((a:ℂ)+(t:ℂ)*Complex.I)*(u:ℂ))) : ℂ).re /
      (∫ u in (0:ℝ)..2, ((2-u)^3*(4+6*u+u^2)/30)*Real.exp (-a*u)) := by
  simpa only [goldbachMiddlePhi,goldbachMiddleReal,goldbachMiddleZ,neg_neg] using
    goldbach_normalized_comparison_from_seven_halves a b t ha hb_lower hb_upper ht

#print axioms solution
