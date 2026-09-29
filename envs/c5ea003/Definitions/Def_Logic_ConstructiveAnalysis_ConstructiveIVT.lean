-- Prove2me | Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveIVT
-- name    : Logic_ConstructiveAnalysis_ConstructiveIVT
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:50:01.748488+00:00
-- url     : https://prove2.me/theorems/ab943d4a-1c60-44a1-8009-54e485fa274c
-- title:
--   Aether Catalog definitions — Logic_ConstructiveAnalysis_ConstructiveIVT
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.ConstructiveAnalysis.ConstructiveIVT`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/ConstructiveAnalysis/ConstructiveIVT.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
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


namespace Bishop

open Set

/-- `ω` is a **modulus of uniform continuity** for `f` on `s`: an explicit map from
accuracies to accuracies, as required in Bishop's definition of a continuous
function on a compact interval. -/
def HasModulusOn (f : ℝ → ℝ) (s : Set ℝ) (ω : ℝ → ℝ) : Prop :=
  ∀ ε > 0, 0 < ω ε ∧ ∀ x ∈ s, ∀ y ∈ s, |x - y| ≤ ω ε → |f x - f y| ≤ ε


/-- The `k`-th point of the uniform grid of `N` subintervals of `[a,b]`. -/
noncomputable def grid (a b : ℝ) (N k : ℕ) : ℝ := a + k * (b - a) / N







/-! ## Exact roots under an explicit non-degeneracy assumption -/

/-- `f` increases at rate at least `c` on `s`: an explicit quantitative form of
"`f` is nowhere locally constant", which is what makes the *exact* intermediate
value theorem constructive. -/
def HasSlopeBoundOn (f : ℝ → ℝ) (s : Set ℝ) (c : ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≤ y → c * (y - x) ≤ f y - f x





/-! ## The root as a Bishop real

Finally we present the root itself as a Bishop real: a regular sequence of
*rationals*, each term of which is one of the explicitly searched grid points. -/

/-- The rational grid point, whose image in `ℝ` is `grid a b N k`. -/
def gridQ (a b : ℚ) (N k : ℕ) : ℚ := a + k * (b - a) / N



end Bishop


