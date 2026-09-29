-- Prove2me | Theorems.Thm_Bishop_exists_grid_abs_le
-- name    : Bishop.exists_grid_abs_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:18:26.644189+00:00
-- url     : https://prove2.me/theorems/18b9f9e9-664e-4a72-9f5c-cf22f52877cd
-- title:
--   Approximate intermediate value theorem with explicit modulus.
-- statement:
--   **Approximate intermediate value theorem with explicit modulus.**
--
--   If `f` has modulus of uniform continuity `ω` on `[a,b]`, if `f a ≤ 0 ≤ f b`, and if
--   `N ≥ 1` is chosen so that the mesh `(b-a)/N` is at most `ω ε`, then one of the `N+1`
--   grid points `a + k(b-a)/N` satisfies `|f| ≤ ε`.  The search is finite and explicit:
--   take the largest `k` with `f (grid k) ≤ 0`.
--
--   ```lean
--   theorem Bishop.exists_grid_abs_le{f : ℝ → ℝ} {a b : ℝ} {ω : ℝ → ℝ} {ε : ℝ} {N : ℕ}
--       (hab : a ≤ b) (hω : HasModulusOn f (Icc a b) ω) (hε : 0 < ε)
--       (hN : 0 < N) (hstep : (b - a) / N ≤ ω ε)
--       (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
--       ∃ k ≤ N, |f (grid a b N k)| ≤ ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/ConstructiveIVT.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/ConstructiveIVT.lean#L82

-- Thm stub generated from Logic/ConstructiveAnalysis/ConstructiveIVT.lean
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

theorem Bishop.exists_grid_abs_le{f : ℝ → ℝ} {a b : ℝ} {ω : ℝ → ℝ} {ε : ℝ} {N : ℕ}
    (hab : a ≤ b) (hω : HasModulusOn f (Icc a b) ω) (hε : 0 < ε)
    (hN : 0 < N) (hstep : (b - a) / N ≤ ω ε)
    (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ k ≤ N, |f (grid a b N k)| ≤ ε := by sorry
