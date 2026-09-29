-- Prove2me | solution 1 for Bishop.exists_grid_near_root
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:37:55.695984+00:00
-- url     : https://prove2.me/submissions/04d41055-61b8-44c5-8cb8-15ad721c0688

-- Sol generated from Logic/ConstructiveAnalysis/RootLocation.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
import Definitions.Def_Logic_ConstructiveAnalysis_RootLocation
import Theorems.Thm_Bishop_HasModulusOn_continuousOn
import Theorems.Thm_Bishop_grid_last
import Theorems.Thm_Bishop_grid_mem_Icc
import Theorems.Thm_Bishop_grid_succ_sub
import Theorems.Thm_Bishop_grid_zero
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











open Bishop in
theorem solution{f : ℝ → ℝ} {a b : ℝ} {ω : ℝ → ℝ} {N : ℕ}
    (hab : a ≤ b) (hω : HasModulusOn f (Icc a b) ω) (hN : 0 < N)
    (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ k ≤ N, ∃ r ∈ Icc a b, f r = 0 ∧ |grid a b N k - r| ≤ (b - a) / N := by
  classical
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hmesh : 0 ≤ (b - a) / N := div_nonneg (by linarith) hN'.le
  set S : Finset ℕ := (Finset.range (N + 1)).filter (fun k => f (grid a b N k) ≤ 0) with hS
  have h0 : 0 ∈ S := by simp [hS, grid_zero, hfa]
  have hne : S.Nonempty := ⟨0, h0⟩
  set k := S.max' hne with hk
  have hkS : k ∈ S := S.max'_mem hne
  have hkrange : k ≤ N :=
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hkS).1)
  have hfk : f (grid a b N k) ≤ 0 := (Finset.mem_filter.mp hkS).2
  refine ⟨k, hkrange, ?_⟩
  rcases eq_or_lt_of_le hkrange with hkN | hkN
  · -- the search reached the right endpoint, where `f` vanishes
    have hgb : grid a b N k = b := by rw [hkN, grid_last hN]
    refine ⟨b, ⟨hab, le_rfl⟩, ?_, ?_⟩
    · rw [hgb] at hfk
      exact le_antisymm hfk hfb
    · rw [hgb, sub_self, abs_zero]
      exact hmesh
  · -- otherwise the next grid point brackets a root
    have hk1 : k + 1 ≤ N := hkN
    have hnot : (k + 1) ∉ S := by
      intro hmem
      have := S.le_max' _ hmem
      omega
    have hpos : 0 < f (grid a b N (k + 1)) := by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), not_lt.mp h⟩)
    have hmem1 : grid a b N k ∈ Icc a b := grid_mem_Icc hab hN hkrange
    have hmem2 : grid a b N (k + 1) ∈ Icc a b := grid_mem_Icc hab hN hk1
    have hsucc : grid a b N (k + 1) - grid a b N k = (b - a) / N := grid_succ_sub
    have hle : grid a b N k ≤ grid a b N (k + 1) := by linarith
    have hsubset : Icc (grid a b N k) (grid a b N (k + 1)) ⊆ Icc a b :=
      Icc_subset_Icc hmem1.1 hmem2.2
    have hcont : ContinuousOn f (Icc (grid a b N k) (grid a b N (k + 1))) :=
      hω.continuousOn.mono hsubset
    have h0mem : (0 : ℝ) ∈ Icc (f (grid a b N k)) (f (grid a b N (k + 1))) :=
      ⟨hfk, hpos.le⟩
    obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc hle hcont h0mem
    refine ⟨r, hsubset hr, hfr, ?_⟩
    rw [abs_of_nonpos (by linarith [hr.1])]
    linarith [hr.2]
