-- Prove2me | Definitions.Def_Algebra_ScanSchemeDecoding_Core
-- name    : Algebra_ScanSchemeDecoding_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:05:58.958327+00:00
-- url     : https://prove2.me/theorems/569993e9-29b8-4da7-a5bc-5db507f742d5
-- title:
--   Aether Catalog definitions — Algebra_ScanSchemeDecoding_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ScanSchemeDecoding.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ScanSchemeDecoding/Core.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Triangle

/-!
# Scan schemes: honest uniqueness decoding and exact cost accounting

A **scan scheme** on a finite key type `α` with bucket labels in `β` is nothing but a
bucket map `bucket : α → β`.  Decoding a key means scanning its bucket, in the
canonical (linear) order, until the key is found.  Two things are then formalised
here, and both are *exact*, not asymptotic:

* **Honest uniqueness decoding** (`ScanScheme.honest_scanCode`,
  `ScanScheme.decode_eq_some_iff`).  The pair `encode x = (bucket x, idx x)`
  — bucket label together with the *intra-bucket index* — decodes back to `x`, and
  it is the **only** pair that does so.  So `encode` is an injection into
  `β × ℕ` whose decoding is unambiguous: no scheme-level ambiguity is hidden in the
  cost model.
* **Exact cost accounting** (`ScanScheme.decodeCost_eq`).  The total decoding cost
  `∑ x, decodeCost x` equals `∑ b, triangle (fiber b).card` *on the nose*.

The two facts together turn the optimisation of scan schemes into the purely
arithmetic problem solved in `Algebra.ScanSchemeDecoding.Triangle`.
-/

namespace ScanSchemeDecoding

open Finset

/-- A scan scheme: a bucket assignment of keys `α` to bucket labels `β`. -/
structure ScanScheme (α β : Type*) where
  /-- The bucket a key is stored in. -/
  bucket : α → β

variable {α β : Type*} [Fintype α] [LinearOrder α] [DecidableEq β]

namespace ScanScheme

variable (S : ScanScheme α β)

/-- The set of keys stored in bucket `b`. -/
def fiber (b : β) : Finset α := {x | S.bucket x = b}

/-- The keys of bucket `b`, in the order in which a scan visits them. -/
def scanList (b : β) : List α := (S.fiber b).sort (· ≤ ·)

/-- The **intra-bucket index** of a key: its position in the scan of its own bucket. -/
def idx (x : α) : ℕ := (S.scanList (S.bucket x)).idxOf x

/-- Decoding cost: the (1-based) number of comparisons a scan performs to find `x`. -/
def decodeCost (x : α) : ℕ := S.idx x + 1

/-- The scan code of a key: bucket label plus intra-bucket index. -/
def encode (x : α) : β × ℕ := (S.bucket x, S.idx x)

/-- Decoding a scan code: read off the entry at the given index of the given bucket. -/
def decode (p : β × ℕ) : Option α := (S.scanList p.1)[p.2]?













end ScanScheme


namespace ScanScheme

variable (S : ScanScheme α β)




end ScanScheme

end ScanSchemeDecoding


