-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_typed_square_support_card_le_six
-- name    : Couret.STROBO2TORS.recoh_typed_square_support_card_le_six
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:43:20.383718+00:00
-- url     : https://prove2.me/theorems/70a4a291-831c-48b6-8e52-8e1fbfd75779
-- title:
--   A formatted typed square has at most six support points
-- statement:
--   Let $L$ be a list of point/multiplicity pairs in any type with decidable equality. Suppose $L$ has between three and six entries with distinct points, multiplicities from one through three totaling nine, and either one or three odd multiplicities. Then
--
--   $$|\{x:(x,m)\in L\text{ for some }m\}|\le6.$$
--
--   This obtains the decoder support bound from the typed input contract.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTypedObservation.lean, lines 70–74; source file SHA-256 5e7a00f9666a5b8cb41765e60b981ccdb33bfeadfb65f8a536d67383af84ce84; theorem Couret.STROBO2TORS.recoh_typed_square_support_card_le_six

import Aesop
import Definitions.Def_Couret_RecohTypedObservation_b23b2e33136b
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
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72

set_option autoImplicit false

/-!
Typed sparse input for the labelled ordered convolution square.

The coefficient function and its covering finite set are constructed from
the same list of position/count entries.  Their consistency is proved,
rather than supplied to the decoder.  The format validator expresses the
numeric checks performed by the Python square reader after coordinates and
integers have been parsed.  Syntactic JSON parsing is not part of this file.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [DecidableEq G]

theorem recoh_typed_square_support_card_le_six
    (entries : List (G × ℕ)) (h : RecohTypedSquareFormat entries) :
    (recohTypedSquareSupport entries).card ≤ 6 := by sorry






end Couret.STROBO2TORS
