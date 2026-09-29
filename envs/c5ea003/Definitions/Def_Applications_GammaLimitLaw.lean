-- Prove2me | Definitions.Def_Applications_GammaLimitLaw
-- name    : Applications_GammaLimitLaw
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:46:16.975344+00:00
-- url     : https://prove2.me/theorems/a98ec9d9-ef67-4c49-8dcc-7b4ca2f0dbeb
-- title:
--   Aether Catalog definitions — Applications_GammaLimitLaw
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.GammaLimitLaw`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/GammaLimitLaw.lean by skeleton subtraction
import Mathlib

/-!
# The limit law for descendants in random `d`-DAGs: the Gamma target distribution

In the random recursive DAG `G_n` with out-degree `d ≥ 2`, the rescaled number of
descendants `|D_n| / n^{1/d}` converges in distribution to a **Gamma distribution with
shape parameter `d` and rate parameter `1`** (Janson, 2023).

This file develops, fully formally, the *target* of that convergence: the Gamma`(d, 1)`
distribution, its density, and — most importantly for the method of moments used to prove
such limit theorems — the complete description of its moments.

The main results are:

* `gammaDensity_integral` : the Gamma`(d,1)` density integrates to `1` (it is a genuine
  probability density);
* `gammaMoment_eq_integral` : the `p`-th moment of the density equals `Γ(d+p)/Γ(d)`;
* `gammaMoment_succ` : the moment recurrence `m_{p+1} = (d+p)·m_p`, which is the exact
  characterisation used in method-of-moments proofs of convergence to Gamma`(d,1)`;
* `gammaMoment_nat_eq_prod` : the integer moments are the rising factorials
  `∏_{i<k} (d+i)`;
* `gammaMoment_one` / `gamma_variance` : the mean is `d` and the variance is `d`.

All densities and moments are taken with respect to Lebesgue measure on `(0, ∞)`.
-/

open Real MeasureTheory
open scoped Real

namespace DDAG

/-- The probability density of the Gamma distribution with shape `d > 0` and rate `1`,
`f(x) = e^{-x} · x^{d-1} / Γ(d)` on `(0, ∞)`. -/
noncomputable def gammaDensity (d x : ℝ) : ℝ := Real.exp (-x) * x ^ (d - 1) / Real.Gamma d

/-- The `p`-th moment of the Gamma`(d,1)` distribution, `Γ(d+p)/Γ(d)`.
For `d = shape` this is exactly the limiting moment of `|D_n| / n^{1/d}`. -/
noncomputable def gammaMoment (d p : ℝ) : ℝ := Real.Gamma (d + p) / Real.Gamma d

/-
The Gamma density is nonnegative on the positive half-line.
-/

/-
The core moment computation: the `p`-th moment of the Gamma`(d,1)` density,
`∫₀^∞ x^p f(x) dx`, equals `Γ(d+p)/Γ(d)`.
-/

/-
The Gamma`(d,1)` density integrates to `1`; it is a genuine probability density.
-/

/-
The zeroth moment is `1`.
-/

/-
The **moment recurrence** `m_{p+1} = (d + p) · m_p`.
This is the identity that pins down the Gamma`(d,1)` law in method-of-moments arguments.
-/

/-
The integer moments are rising factorials: `m_k = ∏_{i<k} (d + i)`.
-/

/-
The mean of Gamma`(d,1)` is `d`.
-/

/-
The second moment of Gamma`(d,1)` is `d(d+1)`.
-/

/-
The variance of Gamma`(d,1)` is `d` (second moment minus mean squared).
-/

end DDAG


