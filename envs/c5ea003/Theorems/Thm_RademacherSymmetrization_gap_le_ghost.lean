-- Prove2me | Theorems.Thm_RademacherSymmetrization_gap_le_ghost
-- name    : RademacherSymmetrization.gap_le_ghost
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:42:28.551333+00:00
-- url     : https://prove2.me/theorems/5d1ae8bd-9c8a-41ce-a221-9347ef0780ee
-- title:
--   Gap le ghost
-- statement:
--   Formal statement of `RademacherSymmetrization.gap_le_ghost` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RademacherSymmetrization.gap_le_ghost{p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hn : 0 < n)
--       (F : Finset (X → ℝ)) (hne : F.Nonempty) (S : Fin n → X) :
--       gap F hne p S ≤ ∑ S' : Fin n → X, wt p S' * ghostGap F hne S S' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Rademacher/Symmetrization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Rademacher/Symmetrization.lean#L139

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


omit [DecidableEq X] in

theorem RademacherSymmetrization.gap_le_ghost{p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) (hn : 0 < n)
    (F : Finset (X → ℝ)) (hne : F.Nonempty) (S : Fin n → X) :
    gap F hne p S ≤ ∑ S' : Fin n → X, wt p S' * ghostGap F hne S S' := by sorry
