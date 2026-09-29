-- Prove2me | Definitions.Def_Geometry_PosetTheory_NonCircular
-- name    : Geometry_PosetTheory_NonCircular
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:47:47.536489+00:00
-- url     : https://prove2.me/theorems/cf5ff2be-40d0-4fca-9ffb-8ab7cfb33031
-- title:
--   Aether Catalog definitions — Geometry_PosetTheory_NonCircular
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.PosetTheory.NonCircular`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/PosetTheory/NonCircular.lean by skeleton subtraction
import Mathlib
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

namespace Combinatorics.NonCircular

variable {α : Type*}

/-- A list is **non-circular** when it has no repeated elements. -/
def IsNonCircular (l : List α) : Prop := l.Nodup



/-- A canonical non-circular enumeration of a `Finset`. -/
noncomputable def order [DecidableEq α] (s : Finset α) : List α := s.toList





end Combinatorics.NonCircular


