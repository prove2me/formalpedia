-- Prove2me | Theorems.Thm_Heisenberg125_Heis_productOneFree_anomalySeq
-- name    : Heisenberg125.Heis.productOneFree_anomalySeq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:51:44.768193+00:00
-- url     : https://prove2.me/theorems/cd21dbe5-3c9d-4192-a1de-04bed40ea873
-- title:
--   `y (xy)^3` is product-one-free over `Heis 2`.
-- statement:
--   **`y (xy)^3` is product-one-free over `Heis 2`.**
--
--   ```lean
--   theorem Heisenberg125.Heis.productOneFree_anomalySeq: ProductOneFree anomalySeq := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/PrimeTwoAnomaly.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/PrimeTwoAnomaly.lean#L31

-- Thm stub generated from Algebra/Heisenberg125/PrimeTwoAnomaly.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
import Definitions.Def_Algebra_Heisenberg125_PrimeTwoAnomaly
/-
# The oddness hypothesis is necessary: `d(H_8) ≥ 4 > 3·2 - 3`

Godara and Sarkar conjecture `d(H_{p^3}) = 3p - 3` for every *odd* prime `p`.
The group `Heis 2` of order `8` (which has exponent `4`, not `2`, so it is not
the exponent-`p` Heisenberg group) shows that the oddness is not cosmetic: the
sequence `y · (xy)^3` is product-one-free of length `4 > 3 = 3·2 - 3`.

This also pins down where our odd-`p` arguments break: for `p = 2` one has
`p ∤ binom p 2`, so `p` equal elements in one coset of the centre need not
multiply to a central element, and `2` is not invertible, so the cocycle
straightening `c ↦ c - (m/2) a²` of `Algebra.Heisenberg125.LineBound` is
unavailable.
-/

open Heisenberg125

open Heis

theorem Heisenberg125.Heis.productOneFree_anomalySeq: ProductOneFree anomalySeq := by sorry
