-- Prove2me | Definitions.Def_MachineLearning_InfinityHierarchy
-- name    : MachineLearning_InfinityHierarchy
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:45:11.543733+00:00
-- url     : https://prove2.me/theorems/3e5dc47a-abaa-43b6-b0b7-1970f7a5b1da
-- title:
--   Aether Catalog definitions — MachineLearning_InfinityHierarchy
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.InfinityHierarchy`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/InfinityHierarchy.lean by skeleton subtraction
import Mathlib
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Different sizes of infinity

This file records Cantor's diagonal theorem, the aleph and beth hierarchies, a
precise formulation of the continuum hypothesis, and a type-theoretic Hartogs
construction.  The diagonal argument is stated directly for functions, so its
mathematical content does not depend on cardinal arithmetic.
-/

open Function Set
open Cardinal Ordinal

universe u

namespace InfinityHierarchy











/-- The continuum hypothesis, expressed as equality of aleph-one and the continuum. -/
def ContinuumHypothesis : Prop :=
  continuum = aleph (1 : Ordinal.{u})



/-- A type representing the successor cardinal of the cardinality of `α`.
This is the type-theoretic Hartogs construction used in this development. -/
def HartogsType (α : Type u) : Type u := (Order.succ (#α)).ord.ToType




end InfinityHierarchy


