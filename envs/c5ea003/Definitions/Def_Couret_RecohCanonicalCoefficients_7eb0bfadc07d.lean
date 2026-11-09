-- Prove2me | Definitions.Def_Couret_RecohCanonicalCoefficients_7eb0bfadc07d
-- name    : Couret_RecohCanonicalCoefficients_7eb0bfadc07d
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:04:19.834971+00:00
-- url     : https://prove2.me/theorems/5824baf7-2bb8-44a3-8cea-3668ea314260
-- title:
--   Canonical sparse cyclotomic coefficient lists
-- statement:
--   Sparse root expressions are lists of exponent/integer-coefficient pairs. Canonical lists have strictly increasing exponents and no zero coefficients. Canonicalization combines all coefficients at each active exponent, deletes zeros, and sorts exponents.
--
--   For root order $p^{k+1}$, the bundle canonicalizes reduced root sums and gives the Python single-root reduction rule: a residue exponent in the final $p^k$ block is replaced by the negatives of the corresponding exponents in the preceding $p-1$ blocks. These definitions support exact list comparison of root values.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCanonicalCoefficients.lean; source file SHA-256 d920e9c13ad1cd37a18406f175fa3c21d46e127b29d51e490e7886f8da6b9549

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
import Mathlib.Data.Finset.Sort
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
import Mathlib.Data.Finset.Sort

set_option autoImplicit false

/-!
Canonical sparse integer coefficient lists.

The Python v0.2 `_terms` routine combines coefficients at equal exponents,
discards zeros, and sorts the remaining exponent/coefficient pairs.  The
definitions below express those operations on already typed lists.  Literal
equality and literal negation of the resulting lists are faithful to the
existing polynomial and complex-value semantics.  JSON parsing and Python
execution are not asserted by this file.
-/

namespace Couret.STROBO2TORS

open Polynomial

/-- Strict exponent order together with exclusion of zero coefficients. -/
def RecohCanonicalTerms (ts : RecohSparseTerms) : Prop :=
  ts.Pairwise (fun a b => a.1 < b.1) ∧ ∀ t ∈ ts, t.2 ≠ 0

/-- Nonzero combined coefficients, using only exponents already present. -/
def recohActiveExponents (ts : RecohSparseTerms) : Finset ℕ :=
  (ts.map Prod.fst).toFinset.filter (fun n => recohSparseCoeff ts n ≠ 0)

/-- Merge repeated exponents, delete zeros, and sort the resulting support.
The definition never allocates a dense vector indexed by the root order. -/
def recohCanonicalizeTerms (ts : RecohSparseTerms) : RecohSparseTerms :=
  ((recohActiveExponents ts).sort (· ≤ ·)).map
    (fun n => (n, recohSparseCoeff ts n))

/-- Canonical output corresponding to the reduced-root accumulation in
`_terms`, with order `p^(k+1)` and step `p^k`. -/
def recohCanonicalRootTerms (p k : ℕ) (es : List ℕ) : RecohSparseTerms :=
  recohCanonicalizeTerms (recohReducedTerms p k es)

/-- Typed version of the quotient/remainder branches in Python `_terms`. -/
def recohPythonRootTerms (p k e : ℕ) : RecohSparseTerms :=
  let r := e % p ^ (k + 1)
  let step := p ^ k
  if r / step < p - 1 then [(r, 1)]
  else (List.range (p - 1)).map (fun j => (r % step + j * step, -1))







































































end Couret.STROBO2TORS


