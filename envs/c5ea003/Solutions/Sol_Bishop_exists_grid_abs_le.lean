-- Prove2me | solution 1 for Bishop.exists_grid_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:36:23.226987+00:00
-- url     : https://prove2.me/submissions/b6c9ae77-14e6-4787-b82c-9802fa327b87

-- Sol generated from Logic/ConstructiveAnalysis/ConstructiveIVT.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
import Theorems.Thm_Bishop_grid_last
import Theorems.Thm_Bishop_grid_mem_Icc
import Theorems.Thm_Bishop_grid_succ_sub
import Theorems.Thm_Bishop_grid_zero
/-
# The constructive intermediate value theorem, with explicit modulus

In Bishop's constructive analysis the classical intermediate value theorem is not
available: from `f a ≤ 0 ≤ f b` one cannot compute a point where `f` vanishes
(see `Logic/ConstructiveAnalysis/BrouwerianCounterexamples.lean`).  What *is*
constructively valid, and what Bishop proves, are:

1. the **approximate intermediate value theorem**: for every `ε > 0` one can
   *compute* a point `x ∈ [a,b]` with `|f x| ≤ ε`, provided `f` comes with a
   modulus of uniform continuity `ω`;
2. the **exact intermediate value theorem** for functions that are, in an explicit
   quantitative sense, non-constant (here: with a positive lower slope bound `c`),
   together with an explicit modulus for the root.

Both are proved below.  The approximate root is produced by an entirely explicit
finite search on the grid `a + k(b-a)/N`, `0 ≤ k ≤ N`, where `N` is any integer with
`(b-a)/N ≤ ω ε`; the witness is the *largest* grid index at which `f` is `≤ 0`.

The final theorem `exists_reg_root` presents the root of such a function as a
Bishop real (a regular sequence of rationals) whose rational approximations are
explicitly grid points of the above finite search.
-/


open Bishop

open Set










/-! ## Exact roots under an explicit non-degeneracy assumption -/






/-! ## The root as a Bishop real

Finally we present the root itself as a Bishop real: a regular sequence of
*rationals*, each term of which is one of the explicitly searched grid points. -/





open Bishop in
theorem solution{f : ℝ → ℝ} {a b : ℝ} {ω : ℝ → ℝ} {ε : ℝ} {N : ℕ}
    (hab : a ≤ b) (hω : HasModulusOn f (Icc a b) ω) (hε : 0 < ε)
    (hN : 0 < N) (hstep : (b - a) / N ≤ ω ε)
    (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ k ≤ N, |f (grid a b N k)| ≤ ε := by
  classical
  set S : Finset ℕ := (Finset.range (N + 1)).filter (fun k => f (grid a b N k) ≤ 0) with hS
  have h0 : 0 ∈ S := by
    simp [hS, grid_zero, hfa]
  have hne : S.Nonempty := ⟨0, h0⟩
  set k := S.max' hne with hk
  have hkS : k ∈ S := S.max'_mem hne
  have hkrange : k ≤ N := by
    have := (Finset.mem_filter.mp hkS).1
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp this)
  have hfk : f (grid a b N k) ≤ 0 := (Finset.mem_filter.mp hkS).2
  refine ⟨k, hkrange, ?_⟩
  rcases eq_or_lt_of_le hkrange with hkN | hkN
  · -- the search reached the right endpoint: there `f` vanishes
    have : f (grid a b N k) = f b := by rw [hkN, grid_last hN]
    rw [this] at hfk ⊢
    have : f b = 0 := le_antisymm hfk hfb
    rw [this]
    simpa using hε.le
  · -- otherwise the next grid point has `f > 0`, and the mesh bound applies
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
    have hdist : |grid a b N k - grid a b N (k + 1)| ≤ ω ε := by
      have h1 : grid a b N k - grid a b N (k + 1) = -((b - a) / N) := by
        have := grid_succ_sub (a := a) (b := b) (N := N) (k := k)
        linarith
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have hnn : 0 ≤ (b - a) / N := by
        apply div_nonneg (by linarith) hN'.le
      rw [h1, abs_neg, abs_of_nonneg hnn]
      exact hstep
    have hmod := (hω ε hε).2 _ hmem1 _ hmem2 hdist
    have hdiff : f (grid a b N (k + 1)) - f (grid a b N k) ≤ ε := by
      have := abs_le.mp hmod
      linarith [this.1]
    rw [abs_of_nonpos hfk]
    linarith
