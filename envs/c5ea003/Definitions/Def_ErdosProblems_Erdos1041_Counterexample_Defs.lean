-- Prove2me | Definitions.Def_ErdosProblems_Erdos1041_Counterexample_Defs
-- name    : ErdosProblems_Erdos1041_Counterexample_Defs
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:55:21.626307+00:00
-- url     : https://prove2.me/theorems/cb7a4b61-b6df-451a-b0b8-9a9e7d12bde0
-- title:
--   The exact degree-seven polynomial and its rational parameters
-- statement:
--   Specifies the exact s=10⁻⁶ instance of ani’s degree-seven construction. Put ε=s², ρ=1−s¹⁶ and
--   \[
--   a=-\frac{329507}{1600}-is,\qquad b=\frac{9s}{5}+i\frac{551827}{800},\qquad c=\frac{23013813}{32000}-\frac{162}{25}is.
--   \]
--   The model polynomial and its contraction are
--   \[
--   F(z)=z^7-1+\varepsilon^4(az^3-\overline a z^4)+\varepsilon^5(bz^2-\overline b z^5)+\varepsilon^6(cz-\overline c z^6),\qquad f(z)=\rho^7F(z/\rho).
--   \]
--   The remaining declarations define rescaled models, the strict lemniscate Ω(p)={z:|p(z)|<1}, total variation on [0,1], and the quadratic factor at a critical point. Separate theorems prove monicity, root location, distinctness and the path bounds.
-- source:
--   Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos1041/Counterexample/Defs.lean#L1-L240
--   Construction by ani: https://www.erdosproblems.com/forum/thread/1041#post-8861
--   Related paper and provenance: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L25-L99
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/1041/erdos-1041-lemniscate-newton-flow.tex#L1662-L1772
--   AI-assisted formalization in Will Cook's project; ani is credited for the degree-seven construction. Independent correspondence of the 1958 Problem 5 wording to this modern formulation is unrecorded.

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/
/-!
External source: ani, erdosproblems.com forum thread 1041, 7 Sept 2026.
Formalisation of the shared interface (constants, polynomials, target statement,
and the slice obligations S1-S5 consumed by S6) from
`ani_degree7_counterexample.tex`.

# Erdős problem #1041: one concrete degree-seven counterexample

Erdős, Herzog and Piranian (1958, Problem 5) asked whether a monic polynomial
with all zeros in the open unit disc must admit a path of length less than two
inside `{z : ‖p z‖ < 1}` joining two of its zeros.  The external paper answers
this negatively with a one-parameter family `f_s`.  This file fixes the single
parameter value `s = 10⁻⁶` and carries the resulting concrete objects.

## What this file is

This file supplies the shared constants, polynomials and proposition-level
interface.  Its three elementary value identities are proved here.  The
formalisation is cut into six proof slices; each slice proves its own
obligations in its own file, and `Assembly.lean` composes those checked results.
No admitted theorem is introduced here.

| slice | file | owns |
|---|---|---|
| S1 | `Algebra.lean` | the exact identities and rational inequalities of §3 |
| S2 | `Components.lean` | Lemma 2.1 part (i) only |
| S3 | `Bottleneck.lean` | Lemma 2.3 and Corollary 2.4 for an arbitrary polynomial |
| S4 | `InstanceCritical.lean` | the concrete root and critical-point data for `f` |
| S5 | `InstanceConnectivity.lean` | the two explicit paths inside `Ω(f)` |
| S7 | `InstanceBarriers.lean` | two explicit barriers in `{‖f‖ ≥ 1}` |
| S6 | `Assembly.lean` | `erdos1041_counterexample` from S1-S5 and S7 |

## Hard rules carried from `FORMALISATION_PLAN.md`

* every constant is an exact rational or Gaussian rational;
* no `Float`, no `native_decide`, no `decide` on a real-number fact;
* admitted axioms are `propext`, `Classical.choice`, `Quot.sound` only;
* a slice never reproves another slice's obligation and never alters its
  statement.

## Provenance

The mathematics is ani's.  We formalise; we did not discover.
-/

noncomputable section

open scoped ComplexConjugate ENNReal

namespace Erdos1041.Counterexample

/-! ## §1  The exact constants

All of §1 is rational.  `s` is the single parameter value at which the whole
formalisation is carried out; `VERIFICATION_RECEIPT.md` records the verified
margins at exactly this `s`.
-/

/-- The parameter of the family, fixed once and for all at `10⁻⁶`.
The receipt checks that the claimed critical-point configuration holds here
(exactly one critical point inside the lemniscate). -/
def s : ℚ := 1 / 10 ^ 6

/-- `ε = s²= 10⁻¹²`, the scaling of the coordinate `z = ρ ε w`. -/
def ε : ℚ := s ^ 2

/-- `ρ = 1 - s¹⁶ = 1 - 10⁻⁹⁶`, the contraction that moves the seven zeros
strictly inside the unit disc. -/
def ρ : ℚ := 1 - s ^ 16

/-- `t = 417/40`, the shape parameter of the model polynomial (paper (3.1)). -/
def t : ℚ := 417 / 40

/-- `A = -5 + 12t - 3t² = -329507/1600` (paper (3.1)). -/
def A : ℚ := -5 + 12 * t - 3 * t ^ 2

/-- `B = -4 + 4t + 6t² = 551827/800` (paper (3.1)). -/
def B : ℚ := -4 + 4 * t + 6 * t ^ 2

/-- `C = t(-8 + 15t - 2t²) = -23013813/32000` (paper (3.1)). -/
def Cconst : ℚ := t * (-8 + 15 * t - 2 * t ^ 2)

theorem A_value : A = -329507 / 1600 := by
  unfold A t; norm_num

theorem B_value : B = 551827 / 800 := by
  unfold B t; norm_num

theorem Cconst_value : Cconst = -23013813 / 32000 := by
  unfold Cconst t; norm_num

/-- `a = A - i s`, a Gaussian rational (paper §1.1). -/
def a : ℂ := (A : ℂ) - (s : ℂ) * Complex.I

/-- `b = i B + (9/5) s`, a Gaussian rational (paper §1.1). -/
def b : ℂ := Complex.I * (B : ℂ) + (9 / 5 : ℚ) * (s : ℂ)

/-- `c = -C - (162/25) i s`, a Gaussian rational (paper §1.1). -/
def c : ℂ := -(Cconst : ℂ) - (162 / 25 : ℚ) * (s : ℂ) * Complex.I

/-! ## §2  The polynomials

`F` is the paper's `F_s` at `s = 10⁻⁶`, written out coefficient by coefficient.
`f z = ρ⁷ F (z / ρ)` is the monic degree-seven counterexample: the rescaling
multiplies the coefficient of `zᵏ` by `ρ^(7-k)`, which is how `f` is spelled
here.  Nothing is divided, so `f` is visibly a polynomial with Gaussian-rational
coefficients.
-/

/-- The paper's `F_s` at `s = 10⁻⁶` (paper (1.3)):
`F z = z⁷ - 1 + ε⁴(a z³ - conj a z⁴) + ε⁵(b z² - conj b z⁵) + ε⁶(c z - conj c z⁶)`. -/
def F : Polynomial ℂ :=
  Polynomial.X ^ 7
    + Polynomial.C (-(ε : ℂ) ^ 6 * conj c) * Polynomial.X ^ 6
    + Polynomial.C (-(ε : ℂ) ^ 5 * conj b) * Polynomial.X ^ 5
    + Polynomial.C (-(ε : ℂ) ^ 4 * conj a) * Polynomial.X ^ 4
    + Polynomial.C ((ε : ℂ) ^ 4 * a) * Polynomial.X ^ 3
    + Polynomial.C ((ε : ℂ) ^ 5 * b) * Polynomial.X ^ 2
    + Polynomial.C ((ε : ℂ) ^ 6 * c) * Polynomial.X
    + Polynomial.C (-1)

/-- The counterexample `f z = ρ⁷ F (z/ρ)` (paper (1.3)), monic of degree seven,
written with the coefficient of `zᵏ` scaled by `ρ^(7-k)`. -/
def f : Polynomial ℂ :=
  Polynomial.X ^ 7
    + Polynomial.C (-(ρ : ℂ) * (ε : ℂ) ^ 6 * conj c) * Polynomial.X ^ 6
    + Polynomial.C (-(ρ : ℂ) ^ 2 * (ε : ℂ) ^ 5 * conj b) * Polynomial.X ^ 5
    + Polynomial.C (-(ρ : ℂ) ^ 3 * (ε : ℂ) ^ 4 * conj a) * Polynomial.X ^ 4
    + Polynomial.C ((ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * a) * Polynomial.X ^ 3
    + Polynomial.C ((ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5 * b) * Polynomial.X ^ 2
    + Polynomial.C ((ρ : ℂ) ^ 6 * (ε : ℂ) ^ 6 * c) * Polynomial.X
    + Polynomial.C (-(ρ : ℂ) ^ 7)

/-! ### The model polynomials of §3 and §4 -/





/-- `P w = -i S(-i w) = w⁷ + A w³ + i B w² - C w` (paper (3.2)). -/
def P : Polynomial ℂ :=
  Polynomial.X ^ 7 + Polynomial.C (A : ℂ) * Polynomial.X ^ 3
    + Polynomial.C (Complex.I * (B : ℂ)) * Polynomial.X ^ 2
    + Polynomial.C (-(Cconst : ℂ)) * Polynomial.X

/-- `G w = -i w³ + (9/5) w² - (162/25) i w` (paper (3.5)).  `Re G` is the
first-order displacement of the lemniscate condition at a critical point of
`P`, and it is positive at exactly one of the six. -/
def G : Polynomial ℂ :=
  Polynomial.C (-Complex.I) * Polynomial.X ^ 3
    + Polynomial.C ((9 / 5 : ℚ) : ℂ) * Polynomial.X ^ 2
    + Polynomial.C (-(162 / 25 : ℚ) * Complex.I) * Polynomial.X

/-- `E_s w = -conj a w⁴ - s⁴ conj b w⁵ - s⁸ conj c w⁶` (paper (4.1)). -/
def E : Polynomial ℂ :=
  Polynomial.C (-conj a) * Polynomial.X ^ 4
    + Polynomial.C (-(s : ℂ) ^ 4 * conj b) * Polynomial.X ^ 5
    + Polynomial.C (-(s : ℂ) ^ 8 * conj c) * Polynomial.X ^ 6

/-- `Q_s = P + s G + s² E_s` (paper (4.1)), the scaled model at `s = 10⁻⁶`.
It satisfies the exact scaling identity `F(ε w) = -1 + ε⁷ Q_s(w)` (paper (4.4)). -/
def Q : Polynomial ℂ :=
  P + Polynomial.C ((s : ℂ)) * G + Polynomial.C ((s : ℂ) ^ 2) * E

/-! ### The ray data of §3.2 -/

















/-- The seventh roots of unity `u_j = e^{2πij/7}` (paper §3.2). -/
def u (j : ℕ) : ℂ := Complex.exp (2 * Real.pi * (j : ℂ) * Complex.I / 7)

/-! ## §3  Lemniscates, components, paths -/

/-- The strict lemniscate `Ω(p) = {z : ‖p z‖ < 1}` (paper §1). -/
def Omega (p : Polynomial ℂ) : Set ℂ := {z : ℂ | ‖p.eval z‖ < 1}

/-- Path length as total variation on `[0,1]`; `⊤` for non-rectifiable paths.
This is the paper's `length(γ)` for a path `γ : [0,1] → ℂ`, with the
convention of §1.3 that the length may be infinite. -/
def pathLength (γ : ℝ → ℂ) : ENNReal := eVariationOn γ (Set.Icc 0 1)

/-- The quadratic factor `𝒜(z) = (p(c+z) - p(c)) / z²` of Corollary 2.4, as a
polynomial by continuation at zero.  This is the correct object only when `c`
is a critical point of `p`, which is the only case in which it is used. -/
def shiftQuad (p : Polynomial ℂ) (cc : ℂ) : Polynomial ℂ :=
  (p.comp (Polynomial.X + Polynomial.C cc) - Polynomial.C (p.eval cc)) /ₘ
    (Polynomial.X ^ 2)

end Erdos1041.Counterexample


