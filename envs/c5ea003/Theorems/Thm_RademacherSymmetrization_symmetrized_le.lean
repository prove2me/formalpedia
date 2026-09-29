-- Prove2me | Theorems.Thm_RademacherSymmetrization_symmetrized_le
-- name    : RademacherSymmetrization.symmetrized_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:42:38.245567+00:00
-- url     : https://prove2.me/theorems/f862d7f2-eec1-4796-b3b3-c4f6ea33daef
-- title:
--   Symmetrized le
-- statement:
--   Formal statement of `RademacherSymmetrization.symmetrized_le` from the Aether Catalog (Logic). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RademacherSymmetrization.symmetrized_le(F : Finset (X → ℝ)) (hne : F.Nonempty) (ε : Fin n → Bool)
--       (q : (Fin n → X) × (Fin n → X)) :
--       F.sup' hne (fun f => (1 / (n:ℝ)) * ∑ i, sgn ε i * (f (q.2 i) - f (q.1 i)))
--         ≤ maxCorr F hne ε q.2 + maxCorr F hne (fun j => !(ε j)) q.1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/Rademacher/Symmetrization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/Rademacher/Symmetrization.lean#L194

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

omit [Fintype X] [DecidableEq X] in

theorem RademacherSymmetrization.symmetrized_le(F : Finset (X → ℝ)) (hne : F.Nonempty) (ε : Fin n → Bool)
    (q : (Fin n → X) × (Fin n → X)) :
    F.sup' hne (fun f => (1 / (n:ℝ)) * ∑ i, sgn ε i * (f (q.2 i) - f (q.1 i)))
      ≤ maxCorr F hne ε q.2 + maxCorr F hne (fun j => !(ε j)) q.1 := by sorry
