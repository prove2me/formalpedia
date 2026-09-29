-- Prove2me | Theorems.Thm_LFunctionUniverse_census_finite
-- name    : LFunctionUniverse.census_finite
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:57:31.426561+00:00
-- url     : https://prove2.me/theorems/d93fa847-ef9d-4d7a-b181-92ce0df2c2fc
-- title:
--   Each census slice is finite.
-- statement:
--   **Each census slice is finite.**
--
--   Below any fixed complexity bound `N` there are only finitely many Selberg data
--   packets.  This is the precise sense in which one can "enumerate the first `100`
--   elements of the Selberg class": each finite prefix of the enumeration is a genuine
--   finite set.
--
--   ```lean
--   theorem LFunctionUniverse.census_finite(N : ℕ) : (census N).Finite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/LFunctionUniverse/SelbergCensus.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/LFunctionUniverse/SelbergCensus.lean#L86

-- Thm stub generated from Applications/LFunctionUniverse/SelbergCensus.lean
import Mathlib
import Definitions.Def_Applications_LFunctionUniverse_SelbergCensus

/-!
# The L-function universe, part III: the Selberg census is countable

An element of the Selberg class is, in practice, determined by a *finite* packet of
arithmetic data:

* its **degree**,
* its **conductor**,
* its **root number** (a complex number of modulus `1`, here modelled by a rational
  numerator/denominator pair), and
* the coefficients of its **Euler factors** at finitely many primes.

We model this packet by the structure `SelbergDatum`.  The two headline results are:

* `instCountableSelbergDatum` / `selbergDatum_countably_infinite`: the space of such
  data packets is **countably infinite** — no bigger than `ℕ` — so there are only
  countably many "well-behaved" L-functions, even though each individual one carries
  infinitely much information.

* `census_finite` together with `census_iUnion`: ordering the packets by a
  complexity bound `N` (a common upper bound on all the numerical invariants,
  refining "ordered by conductor"), the `N`-th slice `census N` is a **finite** set,
  and these finite slices **exhaust** the whole universe.  This is exactly what makes
  a concrete enumeration — "the first `100` elements", and so on — possible.
-/

open scoped Classical

open LFunctionUniverse

theorem LFunctionUniverse.census_finite(N : ℕ) : (census N).Finite := by sorry
