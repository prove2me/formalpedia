-- Prove2me | Theorems.Thm_WeightMonodromy_massey_zero_of_formality
-- name    : WeightMonodromy.massey_zero_of_formality
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:40:57.731422+00:00
-- url     : https://prove2.me/theorems/294361c3-d42c-40a6-8f6e-8877cfa0888a
-- title:
--   Formality kills triple Massey products.
-- statement:
--   **Formality kills triple Massey products.**  If `(A, d)` admits a strict formality zig-zag
--   `A ⊇ sub ↠ sub/idl`, then for cocycles `x, y, z` (with `x, z` in the model `sub`) such that
--   `x * y` and `y * z` bound, one can choose primitives `u, v` for which the Massey representative
--   `s • (u * z) - x * v` bounds as well: the Massey product `⟨x, y, z⟩` contains `0`.
--
--   The hypothesis `hcocycle` records that the Massey representative is a cocycle; in the graded
--   situation of `massey_zero_of_weightPure` this is a consequence of the Leibniz rule.
--
--   ```lean
--   theorem WeightMonodromy.massey_zero_of_formality(F : StrictFormalityData D) {x y z : A}
--       (hx : x ∈ F.sub) (hz : z ∈ F.sub)
--       (hxy_sub : x * y ∈ F.sub) (hyz_sub : y * z ∈ F.sub)
--       (hxy_d : D.d (x * y) = 0) (hyz_d : D.d (y * z) = 0)
--       (hxy_ex : ∃ c, x * y = D.d c) (hyz_ex : ∃ c, y * z = D.d c) (s : k)
--       (hcocycle : ∀ u v : A, D.d u = x * y → D.d v = y * z →
--         D.d (s • (u * z) - x * v) = 0) :
--       ∃ u v w : A, D.d u = x * y ∧ D.d v = y * z ∧ s • (u * z) - x * v = D.d w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/WeightMonodromyMassey.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/WeightMonodromyMassey.lean#L32

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

theorem WeightMonodromy.massey_zero_of_formality(F : StrictFormalityData D) {x y z : A}
    (hx : x ∈ F.sub) (hz : z ∈ F.sub)
    (hxy_sub : x * y ∈ F.sub) (hyz_sub : y * z ∈ F.sub)
    (hxy_d : D.d (x * y) = 0) (hyz_d : D.d (y * z) = 0)
    (hxy_ex : ∃ c, x * y = D.d c) (hyz_ex : ∃ c, y * z = D.d c) (s : k)
    (hcocycle : ∀ u v : A, D.d u = x * y → D.d v = y * z →
      D.d (s • (u * z) - x * v) = 0) :
    ∃ u v w : A, D.d u = x * y ∧ D.d v = y * z ∧ s • (u * z) - x * v = D.d w := by sorry
