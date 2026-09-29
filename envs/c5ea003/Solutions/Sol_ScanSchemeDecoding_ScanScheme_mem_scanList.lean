-- Prove2me | solution 1 for ScanSchemeDecoding.ScanScheme.mem_scanList
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:47:06.486058+00:00
-- url     : https://prove2.me/submissions/bf289980-f978-4e5f-bc20-75fd3b360421

-- Sol generated from Algebra/ScanSchemeDecoding/Core.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
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

open ScanSchemeDecoding

open Finset


variable {α β : Type*} [Fintype α] [LinearOrder α] [DecidableEq β]

open ScanScheme

variable (S : ScanScheme α β)





















open ScanScheme

variable (S : ScanScheme α β)






open ScanSchemeDecoding.ScanScheme in
@[simp] theorem solution{x : α} {b : β} : x ∈ S.scanList b ↔ S.bucket x = b := by
  simp [scanList, fiber]
