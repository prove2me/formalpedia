-- Prove2me | Theorems.Thm_Bishop_exists_reg_root
-- name    : Bishop.exists_reg_root
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:18:40.737603+00:00
-- url     : https://prove2.me/theorems/46e354b8-8931-4391-bd34-4eaf0e7af209
-- title:
--   The root of a constructively presented function is a Bishop real.
-- statement:
--   **The root of a constructively presented function is a Bishop real.**
--
--   Given rational endpoints, a modulus of uniform continuity, and a positive slope
--   bound, the unique root of `f` on `[a,b]` is the limit of a regular sequence of
--   rationals, each term of which is an explicitly computed grid point.
--
--   ```lean
--   theorem Bishop.exists_reg_root{f : ℝ → ℝ} {a b : ℚ} {c : ℝ} {ω : ℝ → ℝ}
--       (hab : a ≤ b) (hc : 0 < c)
--       (hω : HasModulusOn f (Icc (a : ℝ) b) ω) (hslope : HasSlopeBoundOn f (Icc (a : ℝ) b) c)
--       (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
--       ∃ x : Reg, f x.toReal = 0 ∧ x.toReal ∈ Icc (a : ℝ) b ∧
--         ∀ n : ℕ, ∃ N k : ℕ, 0 < N ∧ k ≤ N ∧ x.approx n = gridQ a b N k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/ConstructiveIVT.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/ConstructiveIVT.lean#L246

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










/-! ## Exact roots under an explicit non-degeneracy assumption -/






/-! ## The root as a Bishop real

Finally we present the root itself as a Bishop real: a regular sequence of
*rationals*, each term of which is one of the explicitly searched grid points. -/

theorem Bishop.exists_reg_root{f : ℝ → ℝ} {a b : ℚ} {c : ℝ} {ω : ℝ → ℝ}
    (hab : a ≤ b) (hc : 0 < c)
    (hω : HasModulusOn f (Icc (a : ℝ) b) ω) (hslope : HasSlopeBoundOn f (Icc (a : ℝ) b) c)
    (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ x : Reg, f x.toReal = 0 ∧ x.toReal ∈ Icc (a : ℝ) b ∧
      ∀ n : ℕ, ∃ N k : ℕ, 0 < N ∧ k ≤ N ∧ x.approx n = gridQ a b N k := by sorry
