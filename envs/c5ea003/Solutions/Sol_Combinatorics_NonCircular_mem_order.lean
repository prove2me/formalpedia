-- Prove2me | solution 1 for Combinatorics.NonCircular.mem_order
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:52:43.277731+00:00
-- url     : https://prove2.me/submissions/3db9e205-8c99-4bfe-8453-adddd8355502

-- Sol generated from Geometry/PosetTheory/NonCircular.lean
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










open Combinatorics.NonCircular in
@[simp] theorem solution[DecidableEq α] (s : Finset α) (a : α) :
    a ∈ order s ↔ a ∈ s := Finset.mem_toList
