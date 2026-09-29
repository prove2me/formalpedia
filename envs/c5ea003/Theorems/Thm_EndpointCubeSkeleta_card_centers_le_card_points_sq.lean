-- Prove2me | Theorems.Thm_EndpointCubeSkeleta_card_centers_le_card_points_sq
-- name    : EndpointCubeSkeleta.card_centers_le_card_points_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:48:43.838286+00:00
-- url     : https://prove2.me/theorems/a160423e-c6c7-448a-bd62-281fe6ca440c
-- title:
--   One-dimensional endpoint cardinality theorem.
-- statement:
--   **One-dimensional endpoint cardinality theorem.**
--   If a finite lattice set contains both endpoints of a positive-radius interval
--   about each center, then the number of centers is at most the square of the
--   number of available lattice points.
--
--   ```lean
--   theorem EndpointCubeSkeleta.card_centers_le_card_points_sq    {points centers : Finset ℤ} (hcover : EndpointCovered points centers) :
--       centers.card ≤ points.card ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/EndpointCubeSkeleta/OneDimensional.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/EndpointCubeSkeleta/OneDimensional.lean#L36

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

theorem EndpointCubeSkeleta.card_centers_le_card_points_sq    {points centers : Finset ℤ} (hcover : EndpointCovered points centers) :
    centers.card ≤ points.card ^ 2 := by sorry
