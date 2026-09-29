-- Prove2me | Theorems.Thm_ScanSchemeDecoding_ScanScheme_decodeCost_eq
-- name    : ScanSchemeDecoding.ScanScheme.decodeCost_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:56:43.381985+00:00
-- url     : https://prove2.me/theorems/2eca9289-e614-4e13-b35e-ec8437fab9c3
-- title:
--   Exact cost accounting.
-- statement:
--   **Exact cost accounting.**  The total decoding cost of a scan scheme is exactly the
--   sum of the triangular numbers of its bucket sizes.
--
--   ```lean
--   theorem ScanSchemeDecoding.ScanScheme.decodeCost_eq[Fintype β] :
--       ∑ x, S.decodeCost x = ∑ b, triangle (S.fiber b).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ScanSchemeDecoding/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ScanSchemeDecoding/Core.lean#L174

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

theorem ScanSchemeDecoding.ScanScheme.decodeCost_eq[Fintype β] :
    ∑ x, S.decodeCost x = ∑ b, triangle (S.fiber b).card := by sorry
