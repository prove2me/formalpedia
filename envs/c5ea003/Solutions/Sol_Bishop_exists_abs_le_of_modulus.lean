-- Prove2me | solution 1 for Bishop.exists_abs_le_of_modulus
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:37:54.490682+00:00
-- url     : https://prove2.me/submissions/090cc6fd-d033-4623-a18f-d79942dc7a83

-- Sol generated from Logic/ConstructiveAnalysis/ConstructiveIVT.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
import Theorems.Thm_Bishop_exists_grid_abs_le
import Theorems.Thm_Bishop_grid_mem_Icc
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
theorem solution{f : ℝ → ℝ} {a b : ℝ} {ω : ℝ → ℝ} {ε : ℝ}
    (hab : a ≤ b) (hω : HasModulusOn f (Icc a b) ω) (hε : 0 < ε)
    (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ x ∈ Icc a b, |f x| ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / ω ε)
  have hωpos : 0 < ω ε := (hω ε hε).1
  have hNpos : 0 < N := by
    by_contra h
    push_neg at h
    interval_cases N
    · have : (0 : ℝ) ≤ (b - a) / ω ε := div_nonneg (by linarith) hωpos.le
      simp at hN
      linarith
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hstep : (b - a) / N ≤ ω ε := by
    rw [div_le_iff₀ hN']
    have := (div_lt_iff₀ hωpos).mp hN
    linarith
  obtain ⟨k, hk, hfk⟩ := exists_grid_abs_le hab hω hε hNpos hstep hfa hfb
  exact ⟨grid a b N k, grid_mem_Icc hab hNpos hk, hfk⟩
