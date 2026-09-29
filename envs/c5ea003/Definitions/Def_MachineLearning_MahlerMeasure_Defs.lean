-- Prove2me | Definitions.Def_MachineLearning_MahlerMeasure_Defs
-- name    : MachineLearning_MahlerMeasure_Defs
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:47:31.850396+00:00
-- url     : https://prove2.me/theorems/787ad626-3f1e-441b-bd07-80de8da18cb8
-- title:
--   Aether Catalog definitions — MachineLearning_MahlerMeasure_Defs
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.MahlerMeasure.Defs`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/MahlerMeasure/Defs.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Mahler Measure for Integer Polynomials: Definitions and Root Factorization

This file defines the logarithmic Mahler measure for integer polynomials and proves
the root-factorization formula, which expresses the logarithmic Mahler measure as
a sum of `max(0, log |α|)` over the complex roots.

## Main definitions

- `logMahlerMeasureInt P`: the logarithmic Mahler measure of `P : ℤ[X]`, defined as
  the logarithmic Mahler measure of its complexification.

## Main results

- `logMahlerMeasureInt_eq_sum_roots`: for a monic integer polynomial, the logarithmic
  Mahler measure equals the sum of `max(0, log ‖z‖)` over its complex roots (with multiplicity).
- `logMahlerMeasureInt_nonneg`: for a monic nonzero integer polynomial, the logarithmic
  Mahler measure is nonneg.
- `logMahlerMeasureInt_pos_of_exists_root_norm_gt_one`: if a monic integer polynomial
  has a root outside the unit circle, its logarithmic Mahler measure is strictly positive.
- `logMahlerMeasureInt_eq_zero_iff_all_roots_norm_le_one`: for a monic nonzero integer
  polynomial, the logarithmic Mahler measure is zero iff all roots have norm ≤ 1.

These results build on Mathlib's `Polynomial.logMahlerMeasure` and
`Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots`.
-/

open Polynomial Real Complex

noncomputable section

/-- The logarithmic Mahler measure of an integer polynomial, defined as the logarithmic
Mahler measure of its complexification. -/
noncomputable def logMahlerMeasureInt (P : Polynomial ℤ) : ℝ :=
  (P.map (Int.castRingHom ℂ)).logMahlerMeasure

/-- The (exponential) Mahler measure of an integer polynomial. -/
noncomputable def mahlerMeasureInt (P : Polynomial ℤ) : ℝ :=
  (P.map (Int.castRingHom ℂ)).mahlerMeasure



/-! ### Root factorization formula -/

/-
For a monic integer polynomial, the logarithmic Mahler measure equals the sum of
`max(0, log ‖z‖)` over its complex roots, counted with multiplicity. This is the
fundamental root-factorization formula.
-/

/-! ### Basic properties -/

/-
`max 0 (log ‖z‖)` is nonneg for any complex number.
-/

/-
The sum of `max(0, log ‖z‖)` over any multiset of complex numbers is nonneg.
-/

/-
The logarithmic Mahler measure of a monic integer polynomial is nonneg.
-/

/-
If a monic integer polynomial has a root outside the unit circle, its logarithmic
Mahler measure is strictly positive. This is the entropy-positivity principle:
spectral escape produces measurable complexity.
-/

/-
For a monic nonzero integer polynomial, the logarithmic Mahler measure is zero
if and only if all roots have norm at most 1. This gives a clean reduction principle:
the entire Lehmer barrier is encoded in proving a strict positive gap once a root
escapes the unit circle in a non-cyclotomic way.
-/

/-
One direction: if logMahlerMeasure = 0 then all roots have norm ≤ 1.
-/

/-! ### Multiplicativity -/

/-
The logarithmic Mahler measure is additive under multiplication of monic integer polynomials.
-/

/-! ### Lehmer's reduction principle -/

/-
The Lehmer reduction principle: for a monic nonzero integer polynomial, either the
logarithmic Mahler measure is zero, or there exists a root with norm strictly greater
than 1. This localizes positivity to explicit spectral escape.
-/

end


