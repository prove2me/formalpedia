-- Prove2me | Definitions.Def_Combinatorics_LibraryOfBabelEverything
-- name    : Combinatorics_LibraryOfBabelEverything
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:44:14.593831+00:00
-- url     : https://prove2.me/theorems/93ca1de7-be7d-4efa-b087-5e189c71c502
-- title:
--   Aether Catalog definitions — Combinatorics_LibraryOfBabelEverything
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.LibraryOfBabelEverything`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/LibraryOfBabelEverything.lean by skeleton subtraction
import Mathlib

/-!
# Borges' Library of Babel: finite topology and incompressibility

A book of length `L` over an alphabet of size `A` is a function
`Fin L → Fin A`, equipped here with Mathlib's Hamming metric.

The proposed assertion that this space is both connected and totally
 disconnected is false for a genuine library: its Hamming topology is discrete,
so it is totally disconnected and zero-dimensional, but it is not connected
as soon as `2 ≤ A` and `0 < L`.  The last part of the file gives the precise
finite counting theorem behind the phrase “almost all books are
incompressible”.  Exact Kolmogorov complexity depends on a choice of universal
machine, so the formal result is deliberately uniform in an arbitrary decoder.
-/

open Set Function

namespace LibraryOfBabelEverything

/-- A fixed-length book, carrying the Hamming metric. -/
abbrev Book (A L : ℕ) := Hamming (fun _ : Fin L => Fin A)















end LibraryOfBabelEverything


