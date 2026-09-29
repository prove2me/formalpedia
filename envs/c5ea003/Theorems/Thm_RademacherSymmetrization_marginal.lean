-- Prove2me | Theorems.Thm_RademacherSymmetrization_marginal
-- name    : RademacherSymmetrization.marginal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:42:31.055978+00:00
-- url     : https://prove2.me/theorems/aa2e3a3a-6256-4dbb-8b89-c83cfcf8ce50
-- title:
--   The `i`-th marginal of the product measure is `p`.
-- statement:
--   The `i`-th marginal of the product measure is `p`.
--
--   ```lean
--   theorem RademacherSymmetrization.marginal{p : X → ℝ} (hp1 : ∑ x, p x = 1) (i : Fin n) (g : X → ℝ) :
--       ∑ S : Fin n → X, wt p S * g (S i) = ∑ x, p x * g x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Rademacher/Symmetrization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Rademacher/Symmetrization.lean#L80

-- Thm stub generated from Logic/Rademacher/Symmetrization.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Symmetrization
/-
# The generalization bound: symmetrization

For a finite hypothesis class `F` of real valued functions on a finite domain `X`,
an arbitrary probability vector `p` on `X`, and i.i.d. samples `S ∈ Xⁿ`, the expected
uniform deviation between the true mean and the empirical mean is at most twice the
expected empirical Rademacher complexity:

  `𝔼_S sup_{f ∈ F} (𝔼_p f − Ê_S f) ≤ 2 · 𝔼_S R̂_S(F)`.

This is the classical *symmetrization* inequality, the reason Rademacher complexity
controls generalization.  Everything is finite here: expectations are explicit weighted
sums over `Xⁿ`, so no measure theory is required and the argument is completely
elementary — but not trivial: the heart of the proof is that for each sign pattern `ε`
the map exchanging the `i`-th points of the sample and of the ghost sample whenever
`ε i = false` is a weight preserving involution of `Xⁿ × Xⁿ`.

This file is self-contained.
-/

open RademacherSymmetrization

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X] {n : ℕ}











/-! ### The product measure -/



omit [DecidableEq X] in

theorem RademacherSymmetrization.marginal{p : X → ℝ} (hp1 : ∑ x, p x = 1) (i : Fin n) (g : X → ℝ) :
    ∑ S : Fin n → X, wt p S * g (S i) = ∑ x, p x * g x := by sorry
