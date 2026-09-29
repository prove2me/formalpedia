-- Prove2me | Theorems.Thm_RademacherSymmetrization_generalization_bound
-- name    : RademacherSymmetrization.generalization_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:42:36.676973+00:00
-- url     : https://prove2.me/theorems/c8523df6-fb33-4e27-b0ed-7c2a37d8ba74
-- title:
--   Symmetrization / generalization bound.
-- statement:
--   **Symmetrization / generalization bound.**  The expected uniform deviation of
--   empirical means from true means is at most twice the expected empirical Rademacher
--   complexity of the class.
--
--   ```lean
--   theorem RademacherSymmetrization.generalization_bound{p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
--       (hn : 0 < n) (F : Finset (X → ℝ)) (hne : F.Nonempty) :
--       ∑ S : Fin n → X, wt p S * gap F hne p S
--         ≤ 2 * ∑ S : Fin n → X, wt p S * radS F hne S := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Rademacher/Symmetrization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Rademacher/Symmetrization.lean#L214

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





/-! ### Step 1: introducing the ghost sample -/



/-! ### Step 2: the swapping involution -/





/-! ### Step 3: the symmetrized quantity is bounded by two Rademacher terms -/


/-! ### The generalization bound -/

omit [DecidableEq X] in

theorem RademacherSymmetrization.generalization_bound{p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (hn : 0 < n) (F : Finset (X → ℝ)) (hne : F.Nonempty) :
    ∑ S : Fin n → X, wt p S * gap F hne p S
      ≤ 2 * ∑ S : Fin n → X, wt p S * radS F hne S := by sorry
