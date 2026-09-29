-- Prove2me | Definitions.Def_NumberTheory_EMLQuantumScalarLogRootIsolation
-- name    : NumberTheory_EMLQuantumScalarLogRootIsolation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:05:58.006153+00:00
-- url     : https://prove2.me/theorems/6062ed62-e60f-4422-b4dc-e532ebb17dd6
-- title:
--   Aether Catalog definitions — NumberTheory_EMLQuantumScalarLogRootIsolation
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.EMLQuantumScalarLogRootIsolation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/EMLQuantumScalarLogRootIsolation.lean by skeleton subtraction
import Mathlib

/-!
# High-precision isolation of the quantum EML scalar-log root

This file is the fourth instalment of the *quantum EML scalar logarithm*
thread.  Recall the situation from the earlier catalog files
(`Catalog/NumberTheory/EMLQuantumScalarLog.lean`,
`Catalog/NumberTheory/EMLQuantumScalarLogSharp.lean`,
`Catalog/NumberTheory/EMLQuantumUnitaryExponential.lean`): the raw activation
`exp (i H₁) log (I + i H₂)` is not unitary-valued, but the *scalar* logarithmic
factor `log (1 + t i)` becomes unimodular — hence a unitary of any complex star
algebra — at the unique positive parameter `t` solving

`‖log (1 + t i)‖ = 1`, equivalently `(log (1 + t²)/2)² + (arctan t)² = 1`.

The previous instalments certified this parameter only to lie in `[6/5, 5/4]`,
an interval of width `1/20`.  Since the catalog files are compiled
independently of one another, the basic definitions and the Taylor
certificates of `Catalog/NumberTheory/EMLQuantumTaylorCertificates.lean` are
restated here; everything from `§ 3` on is new.

## Main results

* `QuantumEML.scalarLogRoot` : the root itself, together with
  `QuantumEML.scalarLogNorm_scalarLogRoot` and
  `QuantumEML.eq_scalarLogRoot_of_pos` (uniqueness among positive parameters).
* `QuantumEML.scalarLogRoot_mem_Icc` : **certified isolation of width
  `1.1 · 10⁻⁶`**, namely `scalarLogRoot ∈ [1.2290370, 1.2290381]`; this improves
  the previously certified width `1/20` by a factor of more than `45000`.  The
  proof runs the
  two-sided Taylor certificates for `log` and `arctan` at the two rational
  endpoints, using the Möbius reduction `log x = log 2 + log (x/2)` and the
  tangent addition law `arctan t = π/4 + arctan ((t-1)/(t+1))` to make the
  expansions converge fast enough.
* `QuantumEML.hasDerivAt_scalarLogNormSq` : the closed-form derivative
  `(t log (1 + t²) + 2 arctan t) / (1 + t²)`.
* `QuantumEML.two_div_three_le_deriv_scalarLogNormSq` : the derivative is at
  least `2/3` on `[1, 3/2]`, hence the root is a **simple** zero.
* `QuantumEML.abs_sub_scalarLogRoot_le` : **effective root isolation.**  For
  every `t ∈ [1, 3/2]`, `|t - scalarLogRoot| ≤ (3/2) |scalarLogNormSq t - 1|`;
  any rational witness with small residual is automatically close to the root.
* `QuantumEML.scalarLogRoot_ne_rat_of_den_le` : **effective irrationality
  bound.**  `scalarLogRoot` is not equal to any rational number of denominator
  at most `1287`.  (Number-theoretic input: an interval of width `1.1 · 10⁻⁶`
  around `1.229` contains no fraction of small denominator; this is checked by
  a decision procedure over the `1287` possible denominators.)
* `QuantumEML.bijOn_scalarLogNorm` : the radius map `t ↦ ‖log (1 + t i)‖` is a
  strictly monotone bijection of `[0, ∞)` onto itself, so the unit-circle
  problem is the fibre over `1` of a global order isomorphism.
* `QuantumEML.scalarLogNorm_eq_one_iff` : **complete classification** of the
  solutions: exactly the two parameters `± scalarLogRoot`.
* `QuantumEML.spectral_log_activation_mem_unitary_iff` : **spectral rigidity.**
  A logarithmic activation `V · diag (log (1 + i d)) · V⋆` of a Hermitian matrix
  is unitary iff every eigenvalue equals `± scalarLogRoot`; unitarity therefore
  pins the whole spectrum to two certified transcendental-looking values.
* `QuantumEML.transcendental_scalarLogRoot` : **conditional transcendence.**
  Under the (open) hypothesis that a product of two principal logarithms of
  algebraic numbers is never `1`, the root is transcendental.  The hypothesis is
  an explicit assumption of the theorem, not an axiom.
-/

noncomputable section

open Complex Real Set

namespace QuantumEML

/-! ## 1.  Taylor certificates (restated from `EMLQuantumTaylorCertificates.lean`) -/

namespace Certificates



/-! ### Higher-order certificates: the next rung of the ladder -/







end Certificates

open Certificates

/-! ## 2.  The scalar logarithmic norm (restated) -/

/-- The scalar logarithmic norm along the vertical line through `1`. -/
def scalarLogNorm (t : ℝ) : ℝ := ‖Complex.log (1 + (t : ℂ) * I)‖

/-- Closed form of its square. -/
def scalarLogNormSq (t : ℝ) : ℝ := (Real.log (1 + t ^ 2) / 2) ^ 2 + (Real.arctan t) ^ 2












/-! ## 3.  The certified interval of width `1.1 · 10⁻⁶` -/










/-! ## 4.  The root and its characterisation -/








/-! ## 5.  The derivative, simplicity of the root, and effective isolation -/







/-! ## 6.  Effective irrationality: no rational with denominator `≤ 1287` -/



/-! ## 7.  The radius map is a bijection of `[0, ∞)` -/






/-! ## 8.  Reflection symmetry and the complete classification of solutions -/




/-! ## 9.  Spectral rigidity of unitary logarithmic activations -/

section Spectral

variable {n : Type*} [Fintype n] [DecidableEq n]










end Spectral

/-! ## 10.  Conditional transcendence of the root -/





end QuantumEML


