-- Prove2me | Theorems.Thm_Zeta23_Tail_eventually_tailInputs
-- name    : Zeta23.Tail.eventually_tailInputs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:46:47.802518+00:00
-- url     : https://prove2.me/theorems/0584a807-061d-427b-834a-30f640d39bed
-- title:
--   Proposition [prop:tail] in eventually-in-$T$ form, with explicit $\theta_0$
-- statement:
--   **Setup.** Let $Z$ be an abstract zero configuration and $P$ valid parameters (taper profile $\varrho$, exponent $0 < \lambda \le 1$, width $w \ge 1$); write $L = P.L\,T = \lambda\ell(T)$, $\ell(T)=\log(T/2\pi)$. Assume: (i) $A_0 \ge 1$ and the unit-window local zero count $Z.N\,t\,(t+1) \le A_0\log(|t|+3)$ for all real $t$ (the input `PaperInputs.RvM.local`); (ii) a function $C_1 : \mathbb{R}\to\mathbb{R}$ with $C_1(T) \ge 0$ such that, for all large $T$, the decay bound [eq:hfbound] holds for the taper transform: $\|\hat\varphi_T(r - iy)\| \le e^{L/4}C_1(T)/\|r - iy\|^2$ whenever $|y| \le 1/2$ and $r - iy \ne 0$ (in the concrete instantiation $C_1(T) = \|\varphi''\|_1$, constant in value but a $T$-dependent Lean term); (iii) eventually $a(T) > 0$ (where $a = L^{-1}\int\varphi^2$); (iv) eventually the reflection symmetry $\hat\varphi_T(\bar z) = \overline{\hat\varphi_T(z)}$ for all $z \in \mathbb{C}$. Inputs (ii)–(iv) are all supplied by `Taper.lean`.
--
--   **Statement.** For all sufficiently large $T$, the tail-inputs predicate `Assembly.TailInputs Z P T θ₀(T)` holds with
--   $$\theta_0(T) \;=\; \theta_0\!\bigl(A_0,\, e^{L/4}C_1(T),\, T\bigr) \;=\; \frac{4A_0\,\bigl(e^{L/4}C_1(T)\bigr)^2\log(4T)}{T},$$
--   i.e. $\tilde E = E/L$ is Hermitian with every eigenvalue at most $\theta_0(T)$ in absolute value ("$\|\tilde E\| \le \theta_0$"), and there is $B \ge 0$ with $|\mathrm{tr}\,\hat E| \le B$, $\|\hat E\|_F \le B$ and $B \le \theta_0(T)/(aL)$ ("$\|\hat E\|_1 \le \theta_0/(aL)$"), for $\hat E = E/(aL^2)$.
--
--   **Role.** This packages Proposition [prop:tail] in the filtered (eventually-in-$T$) shape required by the abstract main theorem `thmA_abstract`; it is consumed by `eventually_tailPackage`, which additionally bounds $\theta_0(T) \le C\,\ell(T)\,T^{\lambda/2-1}$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L644-L662, docstring tags [prop:tail], [eq:hfbound]

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne

open Matrix Finset Complex
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg
open Filter
variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

theorem Zeta23.Tail.eventually_tailInputs (Z : ZeroConfig) (P : Params) (hP : P.Valid) {A₀ : ℝ}
    (hA₀ : 1 ≤ A₀) (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (C₁ : ℝ → ℝ) (hC₁ : ∀ T, 0 ≤ C₁ T)
    (hdecay : ∀ᶠ T in atTop, ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
      ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ T / ‖(r : ℂ) - I * y‖ ^ 2)
    (ha : ∀ᶠ T in atTop, 0 < P.a T)
    (hconj : ∀ᶠ T in atTop, ∀ z : ℂ,
      P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    ∀ᶠ T in atTop, Assembly.TailInputs Z P T (theta0 A₀ (Real.exp (P.L T / 4) * C₁ T) T) := by sorry
