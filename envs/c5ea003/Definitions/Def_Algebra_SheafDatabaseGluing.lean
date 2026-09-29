-- Prove2me | Definitions.Def_Algebra_SheafDatabaseGluing
-- name    : Algebra_SheafDatabaseGluing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:12:39.152167+00:00
-- url     : https://prove2.me/theorems/a020655a-bcbf-456c-9528-36a5c9e17662
-- title:
--   Aether Catalog definitions — Algebra_SheafDatabaseGluing
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.SheafDatabaseGluing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/SheafDatabaseGluing.lean by skeleton subtraction
import Mathlib

/-!
# Sheaf-Theoretic Database Gluing

A database view on a set `U` of columns is represented by a dependent function
assigning a value to every column in `U`.  Two views are compatible when their
values agree on `U ∩ V`.  This file proves, in a cumulative chain, the concrete
sheaf gluing theorem for such database views:

1. the canonical glued view restricts to the first view;
2. compatibility makes it restrict to the second view as well;
3. therefore a common extension exists;
4. that common extension is unique.

This is the sheaf condition for the sheaf of dependent records on a discrete
set of columns.  It formalizes the deterministic consistency claim without
assuming a probabilistic missing-data model.
-/

open Classical

namespace SheafDatabaseGluing

variable {ι : Type*} (Value : ι → Type*)

/-- A local database record containing values for precisely the columns in
`U`.  The dependent codomain permits heterogeneous column types. -/
abbrev LocalSection (U : Set ι) := (i : ι) → i ∈ U → Value i

/-- Two local records are compatible when they agree on every column in their
overlap. -/
def Compatible {U V : Set ι} (s : LocalSection Value U)
    (t : LocalSection Value V) : Prop :=
  ∀ i (hiU : i ∈ U) (hiV : i ∈ V), s i hiU = t i hiV

/-- The canonical candidate for gluing two records: use `s` on `U`, and use
`t` on the remaining columns of `V`. -/
noncomputable def glue {U V : Set ι} (s : LocalSection Value U)
    (t : LocalSection Value V) : LocalSection Value (U ∪ V) :=
  fun i hi => if hiU : i ∈ U then s i hiU else t i (hi.resolve_left hiU)





end SheafDatabaseGluing


