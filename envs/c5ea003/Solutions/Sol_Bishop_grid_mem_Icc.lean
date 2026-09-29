-- Prove2me | solution 1 for Bishop.grid_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:34:15.799068+00:00
-- url     : https://prove2.me/submissions/c139e964-4e1e-4a15-9838-26a9114cf9b0

-- Sol generated from Logic/ConstructiveAnalysis/ConstructiveIVT.lean
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
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
theorem solution{a b : ℝ} {N k : ℕ} (hab : a ≤ b) (hN : 0 < N) (hk : k ≤ N) :
    grid a b N k ∈ Icc a b := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
  have hba : (0 : ℝ) ≤ b - a := by linarith
  constructor
  · have : 0 ≤ (k : ℝ) * (b - a) / N := by positivity
    simp only [grid]; linarith
  · have h : (k : ℝ) * (b - a) / N ≤ b - a := by
      rw [div_le_iff₀ hN']
      nlinarith
    simp only [grid]; linarith
