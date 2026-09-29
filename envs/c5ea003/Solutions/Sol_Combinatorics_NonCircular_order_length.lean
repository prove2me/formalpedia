-- Prove2me | solution 1 for Combinatorics.NonCircular.order_length
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:52:43.812931+00:00
-- url     : https://prove2.me/submissions/7074a9c0-ae3c-4f13-ad71-54564949a0e7

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
@[simp] theorem solution[DecidableEq α] (s : Finset α) :
    (order s).length = s.card := Finset.length_toList s
