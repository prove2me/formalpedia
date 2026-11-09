-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_observation_check_reduced
-- name    : Couret.STROBO2TORS.recoh_coefficient_observation_check_reduced
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:09.226125+00:00
-- url     : https://prove2.me/theorems/e069412c-9653-4f7b-8c19-f64644c2d22a
-- title:
--   Reduced coefficient checks agree with sparse checks
-- statement:
--   Let $G$ be an abelian group, $H=G[2]$, $K=G[3]$, and $P_\chi(S)=\sum_{x\in S}\chi(x)$ for a complex additive character $\chi$ (so $\chi(x+y)=\chi(x)\chi(y)$). Write $Q_S$ for ordered-sum counts and $\mathcal O_B(S)=(Q_S,(P_{\chi_i}(S))_i)$ for a bank $B=(\chi_i)$. Let $m\ge0$, $U,S\subseteq G$ finite, $R:G\to\mathbb N$, $p,k:\{0,\ldots,m-1\}\to\mathbb N$, support exponent encodings $E_i$, and observed exponent lists $L_i$. Replacing each $L_i$ by its reduced sparse terms makes the coefficient observation check equal the sparse observation check: $$\operatorname{check}_{\mathrm{coeff}}(U,R,p,k,E,\operatorname{red}(L),S)=\operatorname{check}_{\mathrm{sparse}}(U,R,p,k,E,L,S).$$ No prime hypothesis is needed for this identity of checks.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCoefficientObservations.lean, lines 246–253; source file SHA-256 a214893fb37c3513240d7e15478b624128c990891c03081a0727378779f10685; theorem Couret.STROBO2TORS.recoh_coefficient_observation_check_reduced

import Aesop
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72
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
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2

set_option autoImplicit false

/-!
Exact observation checking from integer cyclotomic coefficients.

Observed readings are supplied directly as lists of pairs `(exponent,
integer coefficient)`.  No conversion from coefficients back to root lists
is used.  Complex values occur only in the interpretation and correctness
theorems; all checkers compare natural numbers and integer coefficients.

The range contract is sufficient for faithful evaluation.  The stronger
typed-format contract also excludes zero coefficients and repeated
exponents, matching the conditions inspected by Python `_read_coefficients`.
It does not certify JSON parsing, Python execution or sorting.
-/

namespace Couret.STROBO2TORS

open Polynomial
open scoped BigOperators





































variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem recoh_coefficient_observation_check_reduced {m : ℕ}
    (U : Finset G) (R : G → ℕ) (p k : Fin m → ℕ)
    (enc : Fin m → Finset G → List ℕ) (obsExp : Fin m → List ℕ) (S : Finset G) :
    recohCoefficientObservationCheck U R p k enc
      (fun i => recohReducedTerms (p i) (k i) (obsExp i)) S =
      recohSparseObservationCheck U R p k enc obsExp S := by sorry


/-!
The coefficient checkers do not themselves establish support coverage,
primality, primitive-root identities or the interpretation of candidate
encodings.  Their correctness theorems display these contracts explicitly.
The observed coefficient values require no witness as a sum of three roots.
Such a representation, if it exists, is supplied by a successfully checked
candidate rather than assumed as an input encoding.

Typed lists may be arbitrarily long.  No constant or bit-complexity bound
for reading or checking observed input is asserted here.  In particular,
the twelve-position bound for comparing two normalized triples is not a
bound on arbitrary externally supplied coefficient lists.
-/


end Couret.STROBO2TORS
