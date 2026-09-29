-- Prove2me | Theorems.Thm_WeightMonodromy_cocycle_mul_coboundary
-- name    : WeightMonodromy.cocycle_mul_coboundary
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:40:55.160248+00:00
-- url     : https://prove2.me/theorems/d55e0391-0071-40da-b345-39586426a302
-- title:
--   A cocycle times a coboundary is a coboundary.
-- statement:
--   A cocycle times a coboundary is a coboundary.
--
--   ```lean
--   theorem WeightMonodromy.cocycle_mul_coboundary{a : A} (ha : D.d a = 0) (c : A) :
--       ∃ e : A, a * D.d c = D.d e := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/WeightMonodromyCohomologyAlgebra.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/WeightMonodromyCohomologyAlgebra.lean#L39

-- Thm stub generated from Novelty/WeightMonodromyCohomologyAlgebra.lean
import Mathlib
import Definitions.Def_Novelty_WeightMonodromyCohomologyAlgebra
import Definitions.Def_Novelty_WeightMonodromyFormality
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# The cohomology algebra of a weight-graded dg-algebra, and its strict diagonal model

Companion to `Catalog/Novelty/WeightMonodromyFormality.lean`.

The first part sets up the multiplicative structure of cohomology for a `WeightedDGA`:
cocycles form a subalgebra and coboundaries a two-sided ideal in it, so that `H = Z / B` is a
`k`-algebra.  Note that the Leibniz rule is only postulated for *bihomogeneous* elements, so
these statements genuinely require the bigraded decomposition (they are proved componentwise).

The second part upgrades formality to its sharpest strict form under purity: the *diagonal*
cocycles (bidegree `(n, n)`, i.e. weight = degree, the shape produced by weight-monodromy)
form a subalgebra `diagAlg` on which the differential vanishes identically and which surjects
onto the cohomology algebra.  Consequently the cohomology algebra of `A` is the quotient of an
honest subalgebra of `A` with zero differential — a *strict multiplicative lift* of `H`.
-/

open WeightMonodromy

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜] (D : WeightedDGA 𝒜)

/-! ### Cocycles form a subalgebra, coboundaries a two-sided ideal -/

theorem WeightMonodromy.cocycle_mul_coboundary{a : A} (ha : D.d a = 0) (c : A) :
    ∃ e : A, a * D.d c = D.d e := by sorry
