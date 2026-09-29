-- Prove2me | Theorems.Thm_EndpointCubeSkeleta_linear_bound_counterexample
-- name    : EndpointCubeSkeleta.linear_bound_counterexample
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:48:51.792264+00:00
-- url     : https://prove2.me/theorems/1cd08254-033c-4fbe-a905-ffd9bd0bed70
-- title:
--   The proposed linear strengthening is false: these four endpoints cover six
-- statement:
--   The proposed linear strengthening is false: these four endpoints cover six
--   integer centers by positive-radius endpoint pairs.
--
--   ```lean
--   theorem EndpointCubeSkeleta.linear_bound_counterexample:
--       EndpointCovered counterexamplePoints counterexampleCenters ∧
--         counterexamplePoints.card < counterexampleCenters.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/EndpointCubeSkeleta/OneDimensional.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/EndpointCubeSkeleta/OneDimensional.lean#L73

-- Thm stub generated from Cryptography/EndpointCubeSkeleta/OneDimensional.lean
import Mathlib
import Definitions.Def_Cryptography_EndpointCubeSkeleta_OneDimensional
/-
# Endpoint cardinality for one-dimensional discrete cube skeleta

This file formalizes the sharp counting mechanism behind the `n = 1, k = 0`
case of the endpoint-cardinality problem.  A zero-dimensional skeleton about an
integer center consists of the two endpoints `c-r` and `c+r`, with `r > 0`.
Recording those labelled endpoints is injective because their sum determines
the center.  Consequently, a finite endpoint set `B` covering a finite center
set `C` satisfies `|C| ≤ |B|²`.

The final theorem refutes the tempting stronger conjecture `|C| ≤ |B|`: four
carefully spaced endpoints cover six distinct centers.
-/

open EndpointCubeSkeleta

open Finset

theorem EndpointCubeSkeleta.linear_bound_counterexample:
    EndpointCovered counterexamplePoints counterexampleCenters ∧
      counterexamplePoints.card < counterexampleCenters.card := by sorry
