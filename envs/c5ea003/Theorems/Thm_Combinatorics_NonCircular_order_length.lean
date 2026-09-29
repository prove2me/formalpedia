-- Prove2me | Theorems.Thm_Combinatorics_NonCircular_order_length
-- name    : Combinatorics.NonCircular.order_length
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:09:26.434603+00:00
-- url     : https://prove2.me/theorems/9a1861e4-7a7c-4e57-9bcf-88596b52c9d2
-- title:
--   Order length
-- statement:
--   Formal statement of `Combinatorics.NonCircular.order_length` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Combinatorics.NonCircular.order_length[DecidableEq α] (s : Finset α) :
--       (order s).length = s.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/PosetTheory/NonCircular.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/PosetTheory/NonCircular.lean#L50

-- Thm stub generated from Geometry/PosetTheory/NonCircular.lean
import Mathlib
import Definitions.Def_Geometry_PosetTheory_NonCircular
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# Non-circular lists

A **non-circular list** is simply a list with no repeated elements (`List.Nodup`).
The terminology emphasises the use we make of it: when we enumerate the elements
of a finite set as a non-circular list `v₀ :: v₁ :: …`, the head `v₀` is distinct
from every later element, so a "star" of merge operations `(v₀, vᵢ)` never pairs a
vertex with itself — there is no self-reference / cycle of length one.

This file provides:

* `Combinatorics.NonCircular.order` — a canonical non-circular enumeration of a `Finset`.
* `order_nodup`, `mem_order`, `order_length` — its basic properties.
* `head_not_mem_tail` — the key "non-circular" fact: the head is not among the tail.
-/

open Combinatorics.NonCircular

variable {α : Type*}








@[simp]

theorem Combinatorics.NonCircular.order_length[DecidableEq α] (s : Finset α) :
    (order s).length = s.card := by sorry
