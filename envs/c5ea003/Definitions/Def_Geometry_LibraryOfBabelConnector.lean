-- Prove2me | Definitions.Def_Geometry_LibraryOfBabelConnector
-- name    : Geometry_LibraryOfBabelConnector
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:51.02597+00:00
-- url     : https://prove2.me/theorems/fab41c8b-643a-417f-a9b8-8d32769a338e
-- title:
--   Aether Catalog definitions — Geometry_LibraryOfBabelConnector
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.LibraryOfBabelConnector`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/LibraryOfBabelConnector.lean by skeleton subtraction
import Mathlib

/-!
# The Library of Babel: topology meets incompressibility

A length-`L` book over an `A`-symbol alphabet is given its Hamming metric.  The
central connector proved here is that a continuous decoder from a connected
parameter space into this library is constant.  Thus geometric connectedness
cannot continuously generate more than one discrete text.

The file also gives the finite counting form of Kolmogorov incompressibility:
when there are fewer descriptions than books, some book has no description,
and at least `A^L - #descriptions` books are undescribed.

The informal demand that a nontrivial finite Hamming library be both connected
and totally disconnected is inconsistent.  We prove total disconnectedness and
prove non-connectedness whenever there are at least two symbols and a nonempty
book.
-/

open Set Function

namespace BabelConnector

/-- Fixed-length books equipped with the Hamming metric. -/
abbrev Book (A L : ℕ) := Hamming (fun _ : Fin L => Fin A)













end BabelConnector


