-- Prove2me | Definitions.Def_Cryptography_EndpointCubeSkeleta_OneDimensional
-- name    : Cryptography_EndpointCubeSkeleta_OneDimensional
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:37.113861+00:00
-- url     : https://prove2.me/theorems/259e4389-5798-4f7b-a933-00cc8a83f7af
-- title:
--   Aether Catalog definitions — Cryptography_EndpointCubeSkeleta_OneDimensional
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.EndpointCubeSkeleta.OneDimensional`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/EndpointCubeSkeleta/OneDimensional.lean by skeleton subtraction
import Mathlib
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

namespace EndpointCubeSkeleta

open Finset

/-- Every center in `centers` has a positive-radius pair of endpoints in `points`. -/
def EndpointCovered (points centers : Finset ℤ) : Prop :=
  ∀ c ∈ centers, ∃ r : ℕ, 0 < r ∧ c - (r : ℤ) ∈ points ∧ c + (r : ℤ) ∈ points



/-- Four endpoints forming a small Sidon-type set. -/
def counterexamplePoints : Finset ℤ := {0, 2, 6, 14}

/-- The six pairwise midpoints of `counterexamplePoints`. -/
def counterexampleCenters : Finset ℤ := {1, 3, 4, 7, 8, 10}




end EndpointCubeSkeleta


