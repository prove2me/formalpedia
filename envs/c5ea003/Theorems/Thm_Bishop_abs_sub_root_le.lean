-- Prove2me | Theorems.Thm_Bishop_abs_sub_root_le
-- name    : Bishop.abs_sub_root_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:18:00.121976+00:00
-- url     : https://prove2.me/theorems/9df7b16c-af27-42f1-93cb-24e93d05a041
-- title:
--   Explicit modulus for the root.
-- statement:
--   **Explicit modulus for the root.**  If `f` has slope bound `c > 0` on `[a,b]`,
--   `r` is a root, and `|f x| ≤ ε`, then `x` is within `ε / c` of `r`.
--
--   ```lean
--   theorem Bishop.abs_sub_root_le{f : ℝ → ℝ} {a b c ε : ℝ} (hc : 0 < c)
--       (hslope : HasSlopeBoundOn f (Icc a b) c)
--       {r x : ℝ} (hr : r ∈ Icc a b) (hfr : f r = 0) (hx : x ∈ Icc a b) (hfx : |f x| ≤ ε) :
--       |x - r| ≤ ε / c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ConstructiveAnalysis/ConstructiveIVT.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ConstructiveAnalysis/ConstructiveIVT.lean#L171

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

theorem Bishop.abs_sub_root_le{f : ℝ → ℝ} {a b c ε : ℝ} (hc : 0 < c)
    (hslope : HasSlopeBoundOn f (Icc a b) c)
    {r x : ℝ} (hr : r ∈ Icc a b) (hfr : f r = 0) (hx : x ∈ Icc a b) (hfx : |f x| ≤ ε) :
    |x - r| ≤ ε / c := by sorry
