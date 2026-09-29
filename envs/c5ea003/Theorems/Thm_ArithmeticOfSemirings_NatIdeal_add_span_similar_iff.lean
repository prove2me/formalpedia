-- Prove2me | Theorems.Thm_ArithmeticOfSemirings_NatIdeal_add_span_similar_iff
-- name    : ArithmeticOfSemirings.NatIdeal.add_span_similar_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:33:54.649129+00:00
-- url     : https://prove2.me/theorems/09147976-4d7a-4d50-a20c-288cc91d3e78
-- title:
--   Adjoining one integral element does not change the similarity class.
-- statement:
--   Adjoining one integral element does not change the similarity class.
--
--   ```lean
--   theorem ArithmeticOfSemirings.NatIdeal.add_span_similar_iff(A : Ideal ℕ) (r : ℕ) :
--       Similar (A + Ideal.span {r}) A ↔ IsIntegralOver A r := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/ArithmeticOfSemiringsIdeals.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/ArithmeticOfSemiringsIdeals.lean#L129

-- Thm stub generated from Tropical/ArithmeticOfSemiringsIdeals.lean
import Mathlib
import Definitions.Def_Tropical_ArithmeticOfSemiringsIdeals

/-!
# The arithmetic of ideals in the natural-number semiring

A formal development of foundational results and a concrete failure of cancellation from
Chen--Hyde--Laurens--Piermarini--Simons, *The Arithmetic of Semirings Part I: Ideals*.
We use Mathlib's existing `Ideal` type for ideals of a semiring.
-/

open ArithmeticOfSemirings







open NatIdeal

theorem ArithmeticOfSemirings.NatIdeal.add_span_similar_iff(A : Ideal ℕ) (r : ℕ) :
    Similar (A + Ideal.span {r}) A ↔ IsIntegralOver A r := by sorry
