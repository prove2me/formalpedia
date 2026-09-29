-- Prove2me | Theorems.Thm_StrangeAttractorsAlgebraic_streamToLimit_injective
-- name    : StrangeAttractorsAlgebraic.streamToLimit_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:37:25.52952+00:00
-- url     : https://prove2.me/theorems/aed7e2c8-090b-42f4-8581-66c3bde2d7ef
-- title:
--   Distinct symbolic trajectories remain distinct in the inverse limit of the
-- statement:
--   Distinct symbolic trajectories remain distinct in the inverse limit of the
--   finite graph approximants.
--
--   ```lean
--   theorem StrangeAttractorsAlgebraic.streamToLimit_injective: Function.Injective streamToLimit := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/StrangeAttractorsAlgebraic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/StrangeAttractorsAlgebraic.lean#L53

-- Thm stub generated from Novelty/StrangeAttractorsAlgebraic.lean
import Mathlib
import Definitions.Def_Novelty_StrangeAttractorsAlgebraic

/-!
# Finite graph approximants and a Cantor inverse limit

Binary de Bruijn graphs give a concrete finite directed-graph model for symbolic
dynamics.  Vertices at level `n` are binary words of length `n + 1`; an edge
records a one-symbol left shift.  Deleting the final symbol is a bonding map of
directed graphs.  Compatible finite prefixes form an inverse limit, and every
infinite binary stream determines a distinct point of that limit.
-/

open StrangeAttractorsAlgebraic

theorem StrangeAttractorsAlgebraic.streamToLimit_injective: Function.Injective streamToLimit := by sorry
