-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_recover_support_square
-- name    : Couret.STROBO2TORS.recoh_indexed_recover_support_square
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:27:56.308934+00:00
-- url     : https://prove2.me/theorems/22ed3986-5e04-412d-b9f8-bfabeac71049
-- title:
--   Indexed sign recovery preserves ordered-square data
-- statement:
--   Let $G$ be an abelian group. Let $e:G[2]\cong\mathbb F_2^J$ be additive and let $b$ assign a Boolean sign vector to each finite support. Indexed recovery translates a support by the two-torsion element with those bits. For any finite support $B$,
--
--   $$Q_{\operatorname{Recover}_{e,b}(B)}=Q_B.$$
--
--   No three-element or correctness assumption on the bit function is needed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohPreparedDecoder.lean, lines 120–127; source file SHA-256 f6373eabc2c71ec81235339b571dd8d279e57b6848a6d8ac04fcaaf979efd104; theorem Couret.STROBO2TORS.recoh_indexed_recover_support_square

import Aesop
import Definitions.Def_Couret_RecohPreparedDecoder_2b97e051dec5
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
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8

set_option autoImplicit false

/-!
Move the square test before sign recovery, as in Python `_prepare_square`.

The generic prepared decoder filters the chosen representatives before
recovery and retains the complete final checker after recovery.  The two
orders give the same answer whenever a final acceptance implies acceptance
of the representative by the precheck.  For the square test, this implication
follows from invariance under every two-torsion translation, for all finite
supports.  The resulting coefficient backend is therefore equal to the
previously certified backend, under the same support-coverage contract.

This module certifies an order of mathematical operations.  It does not
certify the separate Python cache, parser, or runtime.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



















variable {J : Type*}

local notation "H₂" => recohTorsionSubgroup (G := G) 2

theorem recoh_indexed_recover_support_square
    (e : H₂ ≃+ (J → ZMod 2)) (same : Finset G → J → Bool) (B : Finset G) :
    orderedSquare (recohIndexedRecoverSupport e same B) = orderedSquare B := by sorry




variable {I : Type*} [Fintype I]







end Couret.STROBO2TORS
