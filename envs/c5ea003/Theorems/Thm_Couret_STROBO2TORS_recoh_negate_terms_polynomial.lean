-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_negate_terms_polynomial
-- name    : Couret.STROBO2TORS.recoh_negate_terms_polynomial
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:49:16.044186+00:00
-- url     : https://prove2.me/theorems/8e8412b6-1c84-4888-86be-a32ef590b999
-- title:
--   Negating sparse coefficients negates their polynomial
-- statement:
--   Let $L$ be an arbitrary list of integer monomials $(e,c)$, and let $-L$ keep each exponent and negate its coefficient. Then
--
--   $$\sum_{(e,c)\in-L}cX^e=-\sum_{(e,c)\in L}cX^e.$$
--
--   Duplicates, zeros and empty lists are allowed.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file RECOH/lean/RecohCyclotomicNormalization.lean, lines 361–369; source file SHA-256 a32b9cab640a62555c7e6cf6db19b7be429a75e16530887b17a37e8f886e5a45; theorem Couret.STROBO2TORS.recoh_negate_terms_polynomial

import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic

set_option autoImplicit false

/-!
Exact integer-polynomial normalization for primary character sums.

The parameter `k` is one less than the positive primary exponent: the order
is `p ^ (k + 1)` and the stride is `p ^ k`.  Executable reduction uses lists
of integer monomials.  Mathlib's noncomputable integer-polynomial operations
provide their semantics; complex evaluation occurs in correctness theorems.
The separate Python `cyclotomic_sum` implementation is not extracted from,
or certified by, this module.
-/

namespace Couret.STROBO2TORS

open Polynomial
open scoped BigOperators



























/-! ## Executable sparse terms and their polynomial interpretation -/

























/-! ## Executable equality by summing coefficients at present exponents -/

theorem recoh_negate_terms_polynomial (ts : RecohSparseTerms) :
    recohTermsPolynomial (recohNegateTerms ts) = -recohTermsPolynomial ts := by sorry




/-!
## Boundary with the separate Python implementation

`recohRootTerms` uses the same exponent reduction and the same emitted
integer monomials as `cyclotomic_sum` in `../recoh_exact_decoder.py`, with
`order = p ^ (k + 1)` and `stride = p ^ k`.  The Python code subsequently
combines coefficients with `Counter`, omits zeros and sorts by exponent.

The theorems in this module certify the Lean term-list reduction and its
coefficient-summing comparator.  They identify exact equality with equality
of the interpreted integer polynomials and then with complex equality.
They do not certify Python execution, its container operations, parsing,
the extraction of primary orders, or a canonical sorted-list representation.
There is no theorem asserting injectivity of raw monomial lists.

For two normalized triples with prime 2 or 3, the comparator visits at most
twelve exponent positions.  Each test scans both finite term lists.  The
length bounds above do not constitute a bit-complexity theorem: exponent
reduction, integer arithmetic and input reading retain their own costs.
-/


end Couret.STROBO2TORS
