-- Prove2me | Theorems.Thm_ScanSchemeDecoding_ScanScheme_sum_fiber_card
-- name    : ScanSchemeDecoding.ScanScheme.sum_fiber_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:56:47.521+00:00
-- url     : https://prove2.me/theorems/cd6bcb5b-be4f-4bb9-8219-02f97cf4d1d6
-- title:
--   The bucket sizes of a scan scheme sum to the number of keys.
-- statement:
--   The bucket sizes of a scan scheme sum to the number of keys.
--
--   ```lean
--   theorem ScanSchemeDecoding.ScanScheme.sum_fiber_card[Fintype β] : ∑ b, (S.fiber b).card = Fintype.card α := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Core.lean#L186

-- Thm stub generated from Algebra/ScanSchemeDecoding/Core.lean
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



omit [LinearOrder α] in

theorem ScanSchemeDecoding.ScanScheme.sum_fiber_card[Fintype β] : ∑ b, (S.fiber b).card = Fintype.card α := by sorry
