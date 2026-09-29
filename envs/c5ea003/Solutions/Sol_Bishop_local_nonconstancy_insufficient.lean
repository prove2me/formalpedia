-- Prove2me | solution 1 for Bishop.local_nonconstancy_insufficient
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T17:49:23.102369+00:00
-- url     : https://prove2.me/submissions/d0c9be5f-a389-4c92-bf62-3660eac5b9e9

-- Sol generated from Logic/ConstructiveAnalysis/RootLocation.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
import Definitions.Def_Logic_ConstructiveAnalysis_RootLocation
import Theorems.Thm_Bishop_dipFn_abs_ge
import Theorems.Thm_Bishop_dipFn_lipschitz
import Theorems.Thm_Bishop_exists_far_from_critical
/-
# Locating roots: what the grid search really delivers

`Bishop.exists_grid_abs_le` produces a grid point at which `|f|` is small.  Turning a
*small value* into a *small distance to a root* is the delicate step of the
intermediate value theorem, and `Bishop.constructive_ivt` does it with a global slope
bound `c > 0`, at the price of the factor `1/c`.

This file isolates the two sides of that step.

* `Bishop.exists_grid_near_root` : **the bracketing form of the search**.  With no
  non-degeneracy hypothesis whatsoever — only a modulus of uniform continuity and the
  sign condition `f a ≤ 0 ≤ f b` — the *sign-change* grid search returns a grid point
  within one mesh `(b-a)/N` of a genuine root.  The location comes from the bracket
  `f (grid k) ≤ 0 < f (grid (k+1))`, not from the size of `|f|`.

* `Bishop.local_nonconstancy_insufficient` : **a bound on `|f|` alone is not enough**,
  even under Bishop's local non-constancy hypothesis with an explicit modulus `ν`.
  The `1`-Lipschitz function `Bishop.dipFn η x = min (x-1) (|x-3| + η)` has the unique
  root `1`, satisfies local non-constancy with the explicit modulus `ν h = h/8`, and
  yet `|dipFn η 3| = η` is as small as one likes while `3` is at distance `2` from the
  root.  So no theorem of the form "`|f x|` small ⟹ `x` near a root" can be derived
  from local non-constancy alone.
-/


open Bishop

open Set

/-! ## 1. The bracketing form of the grid search -/


/-! ## 2. Local non-constancy does not locate approximate roots

Bishop's exact intermediate value theorem replaces a slope bound by *local
non-constancy*.  The following explicit function shows that this hypothesis, even
with an explicit modulus `ν`, does not let one conclude that a point with small
`|f|` is close to a root. -/



/-- The identity is an explicit modulus of uniform continuity for `dipFn η`. -/
theorem dipFn_hasModulus (η : ℝ) (s : Set ℝ) : HasModulusOn (dipFn η) s id :=
  fun _ε hε => ⟨hε, fun x _ y _ h => (dipFn_lipschitz η x y).trans h⟩

lemma dipFn_zero_le (η : ℝ) : dipFn η 0 ≤ 0 := by
  have : dipFn η 0 ≤ (0 : ℝ) - 1 := min_le_left _ _
  linarith

lemma dipFn_four_nonneg (η : ℝ) (hη : 0 < η) : 0 ≤ dipFn η 4 := by
  have h1 : (0 : ℝ) ≤ (4 : ℝ) - 1 := by norm_num
  have h2 : (0 : ℝ) ≤ |(4 : ℝ) - 3| + η := by positivity
  exact le_min h1 h2

/-- The only root of `dipFn η` is `x = 1`. -/
theorem dipFn_root_unique {η r : ℝ} (hη : 0 < η) (h : dipFn η r = 0) : r = 1 := by
  have habs : 0 ≤ |r - 3| := abs_nonneg _
  simp only [dipFn] at h
  rcases min_cases (r - 1) (|r - 3| + η) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h <;> linarith





open Bishop in
theorem solution{δ : ℝ} (hδ0 : 0 < δ) (hδ2 : δ < 2) :
    ∃ (f : ℝ → ℝ) (ν : ℝ → ℝ) (x : ℝ),
      HasModulusOn f (Icc (0 : ℝ) 4) id ∧ f 0 ≤ 0 ∧ 0 ≤ f 4 ∧
        (∀ h > 0, 0 < ν h) ∧
        (∀ h > 0, ∀ p q : ℝ, p + h ≤ q → ∃ z ∈ Icc p q, ν h ≤ |f z|) ∧
        x ∈ Icc (0 : ℝ) 4 ∧ |f x| ≤ ν δ / 2 ∧ ∀ r : ℝ, f r = 0 → δ < |x - r| := by
  have hη : 0 < δ / 32 := by linarith
  refine ⟨dipFn (δ / 32), fun h => h / 8, 3, dipFn_hasModulus _ _,
    dipFn_zero_le _, dipFn_four_nonneg _ hη, fun h hh => by linarith, ?_,
    ⟨by norm_num, by norm_num⟩, ?_, ?_⟩
  · intro h hh p q hpq
    obtain ⟨z, hz, h1, h3⟩ := exists_far_from_critical hh hpq
    exact ⟨z, hz, dipFn_abs_ge hη h1 h3⟩
  · have h3 : dipFn (δ / 32) 3 = δ / 32 := by
      simp only [dipFn]
      rw [show (3 : ℝ) - 3 = 0 by ring, abs_zero, zero_add]
      exact min_eq_right (by linarith)
    rw [h3, abs_of_pos hη]
    linarith
  · intro r hr
    rw [dipFn_root_unique hη hr]
    rw [show |(3 : ℝ) - 1| = 2 by rw [show (3 : ℝ) - 1 = 2 by ring]; exact abs_of_pos (by norm_num)]
    exact hδ2
