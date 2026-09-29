-- Prove2me | Theorems.Thm_WeightMonodromy_massey_zero_of_weightPure
-- name    : WeightMonodromy.massey_zero_of_weightPure
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:41:26.605643+00:00
-- url     : https://prove2.me/theorems/e1feb174-3583-4349-bfe2-9ded184f014e
-- title:
--   Purity kills triple Massey products.
-- statement:
--   **Purity kills triple Massey products.**  Let `x, y, z` be bihomogeneous cocycles on the
--   diagonal (degree = weight, the shape imposed by weight-monodromy), with `x * y` and `y * z`
--   exact.  If the weight grading is pure then there are primitives `u` of `x * y` and `v` of
--   `y * z` for which the Massey representative `sgn p • (u * z) - x * v` is exact.
--
--   The proof is a pure weight count: choosing `u` and `v` bihomogeneous, the representative has
--   cohomological degree `p + q + r - 1` but weight `p + q + r`, and purity forces every cocycle
--   off the diagonal to be a coboundary.
--
--   ```lean
--   theorem WeightMonodromy.massey_zero_of_weightPure(hpure : IsWeightPure D) {p q r : ℤ} {x y z : A}
--       (hx : x ∈ 𝒜 (p, p)) (hy : y ∈ 𝒜 (q, q)) (hz : z ∈ 𝒜 (r, r))
--       (hdx : D.d x = 0) (hdz : D.d z = 0)
--       {u₀ v₀ : A} (hu₀ : D.d u₀ = x * y) (hv₀ : D.d v₀ = y * z) :
--       ∃ u v c : A, D.d u = x * y ∧ D.d v = y * z ∧
--         D.sgn p • (u * z) - x * v = D.d c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/WeightMonodromyMassey.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/WeightMonodromyMassey.lean#L64

-- Thm stub generated from Novelty/WeightMonodromyMassey.lean
import Mathlib
import Definitions.Def_Novelty_WeightMonodromyFormality
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Massey products, purity and the obstruction to weight-monodromy

Companion to `Catalog/Novelty/WeightMonodromyFormality.lean`.

Two complementary results are proved.

* `massey_zero_of_formality` : in any strictly formal dg-algebra (i.e. one admitting a
  `StrictFormalityData`) every triple Massey product which is defined contains `0`.  The
  mechanism is that the primitives can be chosen inside the acyclic ideal, which is absorbing.

* `massey_zero_of_weightPure` : the same conclusion directly from purity of the weight grading,
  by a *weight* argument: a Massey representative of cohomological degree `p + q + r - 1`
  necessarily has weight `p + q + r`, and purity kills everything off the diagonal.
  The primitives are moreover produced explicitly as bihomogeneous components.

* `not_weightPure_of_massey` : contrapositive.  A space whose cohomology algebra carries a
  genuinely non-vanishing triple Massey product cannot have a pure weight grading; this is the
  algebraic shadow of the non-formal rigid-analytic surfaces, which are therefore obstructions
  to the naive weight-monodromy purity in the corresponding dg-algebra model.
-/

open WeightMonodromy

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜] {D : WeightedDGA 𝒜}



variable (D)

theorem WeightMonodromy.massey_zero_of_weightPure(hpure : IsWeightPure D) {p q r : ℤ} {x y z : A}
    (hx : x ∈ 𝒜 (p, p)) (hy : y ∈ 𝒜 (q, q)) (hz : z ∈ 𝒜 (r, r))
    (hdx : D.d x = 0) (hdz : D.d z = 0)
    {u₀ v₀ : A} (hu₀ : D.d u₀ = x * y) (hv₀ : D.d v₀ = y * z) :
    ∃ u v c : A, D.d u = x * y ∧ D.d v = y * z ∧
      D.sgn p • (u * z) - x * v = D.d c := by sorry
