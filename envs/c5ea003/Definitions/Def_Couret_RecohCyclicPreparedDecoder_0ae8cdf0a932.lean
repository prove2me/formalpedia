-- Prove2me | Definitions.Def_Couret_RecohCyclicPreparedDecoder_0ae8cdf0a932
-- name    : Couret_RecohCyclicPreparedDecoder_0ae8cdf0a932
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:09:08.158426+00:00
-- url     : https://prove2.me/theorems/5f14682a-c2c2-49a7-974c-ae368456f6c5
-- title:
--   Prepared cyclic coefficient decoder
-- statement:
--   This defines the cyclic prepared core by instantiating the early coefficient backend with typed square entries, the product half solver, standard binary coordinates and canonical cyclic bank encodings. The checked version uses the same cyclic input validator and returns the empty set on failure.
--
--   The preparation stage performs early candidate checks before recovery while retaining the same intended exact-observation filtering interface.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclicPreparedDecoder.lean; source file SHA-256 ce438f7797a7d8114b2cc91e6f9398133f55bd0477b80c4f3fbaf12545a1e818

import Aesop
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCyclicCoefficientDecoder_9d7602a6d6c9
import Definitions.Def_Couret_RecohEarlySignChecks_6186d05e32eb

set_option autoImplicit false

/-!
The concrete cyclic decoder with early square and reading checks.

All bank parameters, coefficient encodings, binary coordinates, and square
support data are constructed by the cyclic interface.  This module uses
those data in the early-rejection control flow: check the representative's
square and binary/ternary readings, recover its translation, then retain the
independent full final check.  The guarded decoder is equal to the complete
typed coefficient decoder for every input, including rejected input.

The equality relates executable Lean definitions on typed data.  It does
not identify the external Python parser, caches, or runtime with those
definitions, nor does the candidate bound assert bit complexity.
-/

namespace Couret.STROBO2TORS

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

/-- The canonical cyclic core with square and reading checks before recovery. -/
def recohCyclicPreparedCore
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms) :
    Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  recohEarlyCoefficientBackendDecoder
    (recohTypedSquareSupport entries) (recohTypedSquareValue entries)
    (recohProductHalf q) (recohProductTwoCoordinates q)
    (recohCyclicBankPrime q) (recohCyclicBankDepth q) (recohCyclicBankEncoding q) terms



/-- The same typed input guard as the coefficient decoder, followed by
the concrete early-rejection core. -/
def recohCyclicPreparedDecoder
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohCyclicBankIndex q → RecohSparseTerms) :
    Finset (Finset ((i : Fin d) → ZMod (q i))) :=
  if recohCyclicInputCheck q entries terms then recohCyclicPreparedCore q entries terms
  else ∅











end Couret.STROBO2TORS


