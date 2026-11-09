-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_readings_check_iff
-- name    : Couret.STROBO2TORS.recoh_coefficient_readings_check_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:18.272976+00:00
-- url     : https://prove2.me/theorems/194a25fe-2ab0-41f2-8be6-70737b90bca1
-- title:
--   Coefficient readings check exactly matches all character readings
-- statement:
--   Let $G$ be a finite abelian group. For a character $\chi:G\to\mathbb C$ write $P_\chi(S)=\sum_{x\in S}\chi(x)$, and for a bank $(\chi_i)$ write $\operatorname{Obs}(S)=(Q_S,(P_{\chi_i}(S))_i)$, where $Q_S(z)$ counts ordered pairs from $S$ summing to $z$. The exact decoder of $(R,o)$ consists of all three-element supports $S$ with $\operatorname{Obs}(S)=(R,o)$. Let $I$ be finite. For each $i$, choose prime $p_i$, depth $k_i$, primitive root $\zeta_i$ of order $p_i^{k_i+1}$, reduced coefficient data $T_i$ of value $o_i$, and an exponent encoding $E_i(S)$ of the reading $P_{\chi_i}(S)$. Reduced means all exponents are below $(p_i-1)p_i^{k_i}$. Then
--
--   $$\operatorname{ReadingsCheck}(S)=\mathrm{true}\Longleftrightarrow(P_{\chi_i}(S))_i=o.$$
--
--   No cardinality premise on $S$ is needed for this check equivalence.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCoefficientObservations.lean, lines 186–208; source file SHA-256 a214893fb37c3513240d7e15478b624128c990891c03081a0727378779f10685; theorem Couret.STROBO2TORS.recoh_coefficient_readings_check_iff

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_match_iff
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

omit [DecidableEq G] in
theorem recoh_coefficient_readings_check_iff {I : Type*} [Fintype I]
    (p k : I → ℕ) (enc : I → Finset G → List ℕ) (obsTerms : I → RecohSparseTerms)
    (S : Finset G) (bank : I → AddChar G ℂ) (ζ obs : I → ℂ)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hterms : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i, ((enc i S).map (ζ i ^ ·)).sum = recohSupportProbe (bank i) S)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i) :
    recohCoefficientReadingsCheck p k enc obsTerms S = true ↔
      (fun i => recohSupportProbe (bank i) S) = obs := by sorry










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
