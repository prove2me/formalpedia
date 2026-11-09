-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_all_coefficient_formats_iff
-- name    : Couret.STROBO2TORS.recoh_all_coefficient_formats_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:56:30.788351+00:00
-- url     : https://prove2.me/theorems/962e2c00-e3a3-4eda-9237-5478e515e836
-- title:
--   The bank-wide coefficient format check is exact
-- statement:
--   A sparse term list consists of integer monomials $(e,c)$, representing $\sum cX^e$. It is reduced for $(p,k)$ when all exponents are less than $(p-1)p^k$, and is in coefficient format when it is reduced, its exponents are distinct, and all coefficients are nonzero. Let $I$ be a finite index type, $p,k:I\to\mathbb N$, and $L_i$ sparse term lists. Then
--
--   $$\operatorname{allFormats}(p,k,L)=\mathrm{true}\iff\forall i\in I,\ L_i\text{ is in coefficient format for }(p_i,k_i).$$
--
--   The finite index type may be empty; primality is not required for this syntactic format check.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohTypedObservation.lean, lines 81–85; source file SHA-256 5e7a00f9666a5b8cb41765e60b981ccdb33bfeadfb65f8a536d67383af84ce84; theorem Couret.STROBO2TORS.recoh_all_coefficient_formats_iff

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_format_check_iff
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

theorem recoh_all_coefficient_formats_iff {I : Type*} [Fintype I]
    (p k : I → ℕ) (terms : I → RecohSparseTerms) :
    recohAllCoefficientFormats p k terms = true ↔
      ∀ i, RecohCoefficientFormat (p i) (k i) (terms i) := by sorry


end Couret.STROBO2TORS
