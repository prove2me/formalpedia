-- Prove2me | Theorems.Thm_Bishop_exists_abs_le_of_modulus
-- name    : Bishop.exists_abs_le_of_modulus
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:19:06.617705+00:00
-- url     : https://prove2.me/theorems/7dc1a075-d23c-4288-9ccc-7cfb168d5667
-- title:
--   Approximate intermediate value theorem, existential form.
-- statement:
--   **Approximate intermediate value theorem, existential form.**  For a function
--   with a modulus of uniform continuity on `[a,b]` and `f a ≤ 0 ≤ f b`, every accuracy
--   `ε > 0` is met by some point of `[a,b]`.
--
--   ```lean
--   theorem Bishop.exists_abs_le_of_modulus{f : ℝ → ℝ} {a b : ℝ} {ω : ℝ → ℝ} {ε : ℝ}
--       (hab : a ≤ b) (hω : HasModulusOn f (Icc a b) ω) (hε : 0 < ε)
--       (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
--       ∃ x ∈ Icc a b, |f x| ≤ ε := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/ConstructiveIVT.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/ConstructiveIVT.lean#L139

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

theorem Bishop.exists_abs_le_of_modulus{f : ℝ → ℝ} {a b : ℝ} {ω : ℝ → ℝ} {ε : ℝ}
    (hab : a ≤ b) (hω : HasModulusOn f (Icc a b) ω) (hε : 0 < ε)
    (hfa : f a ≤ 0) (hfb : 0 ≤ f b) :
    ∃ x ∈ Icc a b, |f x| ≤ ε := by sorry
