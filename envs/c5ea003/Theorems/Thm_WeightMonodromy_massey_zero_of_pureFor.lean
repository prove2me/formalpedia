-- Prove2me | Theorems.Thm_WeightMonodromy_massey_zero_of_pureFor
-- name    : WeightMonodromy.massey_zero_of_pureFor
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:41:58.261903+00:00
-- url     : https://prove2.me/theorems/f55f5b0f-460e-4d61-b92b-ad1daa311a4b
-- title:
--   Massey products vanish for any positive weight normalisation.
-- statement:
--   **Massey products vanish for any positive weight normalisation.**  For diagonal
--   bihomogeneous cocycles `x, y, z` of degrees `p, q, r` and weights `wt p, wt q, wt r`, purity
--   along the line `w = wt n` forces the triple Massey product to contain `0`.  The weight excess of
--   the Massey representative is `wt 1 > 0`, which is exactly what purity kills; for the degenerate
--   normalisation `wt = 0` the argument (and the conclusion) would fail.
--
--   ```lean
--   theorem WeightMonodromy.massey_zero_of_pureFor(hwt : 0 < wt 1) (hpure : IsPureFor D wt) {p q r : ℤ} {x y z : A}
--       (hx : x ∈ 𝒜 (p, wt p)) (hy : y ∈ 𝒜 (q, wt q)) (hz : z ∈ 𝒜 (r, wt r))
--       (hdx : D.d x = 0) (hdz : D.d z = 0)
--       {u₀ v₀ : A} (hu₀ : D.d u₀ = x * y) (hv₀ : D.d v₀ = y * z) :
--       ∃ u v c : A, D.d u = x * y ∧ D.d v = y * z ∧
--         D.sgn p • (u * z) - x * v = D.d c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/WeightMonodromyScaled.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/WeightMonodromyScaled.lean#L474

-- Thm stub generated from Novelty/WeightMonodromyScaled.lean
import Mathlib
import Definitions.Def_Novelty_WeightMonodromyFormality
import Definitions.Def_Novelty_WeightMonodromyScaled
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Formality for arbitrary weight normalisations

`Catalog/Novelty/WeightMonodromyFormality.lean` proves that a weight-graded dg-algebra whose
cohomology is pure *with weight equal to the cohomological degree* is formal.  In arithmetic
practice the normalisation varies: with Tate twists the interesting weight of `H^n` is `2n`
rather than `n`, and comparison isomorphisms may rescale weights by any fixed positive factor.

This file removes the normalisation.  Fix an additive map `wt : ℤ →+ ℤ` with `0 < wt 1`
(equivalently `wt n = α n` with `α > 0`) and call a weight-graded dg-algebra `wt`-pure if its
cohomology in bidegree `(n, w)` vanishes for `w ≠ wt n`.  The main theorem
`formality_of_pureFor` produces the same strict formality zig-zag `A ⊇ A' ↠ A'/J` in this
generality, with `A'` the weight-wise canonical truncation *along the line `w = wt n`*.

The case `wt = id` recovers `formality_of_weight_purity` (see `isPureFor_id_iff`).

Note that when `α > 1` the line `w = wt n` misses most weights: for a weight `w` outside the
image of `wt` the whole weight-`w` subcomplex is acyclic and the truncation must discard it
entirely.  This is why the pieces below are indexed by pairs *(degree, diagonal index)* rather
than by bidegrees.
-/

open WeightMonodromy

open scoped Classical

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜]


variable (wt : ℤ →+ ℤ)





variable (D : WeightedDGA 𝒜) (wt : ℤ →+ ℤ)

















/-! ### Multiplicative structure -/









/-! ### Componentwise detection -/





/-! ### The main theorem -/

theorem WeightMonodromy.massey_zero_of_pureFor(hwt : 0 < wt 1) (hpure : IsPureFor D wt) {p q r : ℤ} {x y z : A}
    (hx : x ∈ 𝒜 (p, wt p)) (hy : y ∈ 𝒜 (q, wt q)) (hz : z ∈ 𝒜 (r, wt r))
    (hdx : D.d x = 0) (hdz : D.d z = 0)
    {u₀ v₀ : A} (hu₀ : D.d u₀ = x * y) (hv₀ : D.d v₀ = y * z) :
    ∃ u v c : A, D.d u = x * y ∧ D.d v = y * z ∧
      D.sgn p • (u * z) - x * v = D.d c := by sorry
