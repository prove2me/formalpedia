-- Prove2me | Definitions.Def_MediumPNT_defs
-- name    : MediumPNT_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T14:50:35.069315+00:00
-- url     : https://prove2.me/theorems/0d31ad44-d5d8-486e-99f8-712af4baa378
-- title:
--   Smoothed Chebyshev function $\psi_\epsilon(X)$ as a vertical contour integral, its rectangle-contour pieces $I_1,\dots,I_9$, and zero-free-region bounds on $\zeta'/\zeta$
-- statement:
--   This bundle defines the central analytic objects of the medium-strength prime number theorem (error term $O(X\exp(-c(\log X)^{1/10}))$): a smoothed version of the Chebyshev function expressed by Mellin inversion as a contour integral of $-\zeta'/\zeta$, and the decomposition of that contour into the pieces of a rectangle.
--
--   **Main definitions.** Throughout, $\Lambda$ is the von Mangoldt function, $\zeta$ the Riemann zeta function, $\mathcal{M}$ the Mellin transform, and $\widetilde{1_\epsilon} = \mathrm{Smooth1}\,F\,\epsilon$ a smoothed indicator of $(0,1]$ built from a smoothing kernel $F$ at scale $\epsilon$.
--
--   - `SmoothedChebyshevIntegrand F ε X` — the integrand $s \mapsto \dfrac{-\zeta'(s)}{\zeta(s)}\, \mathcal{M}(\widetilde{1_\epsilon})(s)\, X^s$.
--
--   - `SmoothedChebyshev F ε X` — the smoothed Chebyshev function $\psi_\epsilon(X) = \frac{1}{2\pi i}\int_{(\sigma_0)} \frac{-\zeta'(s)}{\zeta(s)}\,\mathcal{M}(\widetilde{1_\epsilon})(s)\,X^s\,ds$, a vertical line integral at $\sigma_0 = 1 + (\log X)^{-1}$; by Mellin inversion it equals $\sum_n \Lambda(n)\,\widetilde{1_\epsilon}(n/X)$.
--
--   - `I₁, I₂, I₃, I₄, I₅, I₆, I₇, I₈, I₉` and the combined piece `I₃₇` — the nine contour integrals obtained by pulling the vertical contour from $\Re s = \sigma_0$ into the zero-free region: the far tails $|t| \ge T$ on the line $\sigma_0$ ($I_1, I_9$), the horizontal crossings at height $\pm T$ ($I_2, I_8$), the vertical segments on the shifted line $\sigma_1$ for $3 \le |t| \le T$ ($I_3, I_7$, jointly $I_{37}$), the horizontal segments at height $\pm 3$ between $\sigma_2$ and $\sigma_1$ ($I_4, I_6$), and the innermost vertical segment at $\sigma_2$ for $|t| \le 3$ ($I_5$), each normalized by $\frac{1}{2\pi i}$.
--
--   - `LogDerivZetaHasBound A C` — the proposition that $\left\lVert \frac{\zeta'}{\zeta}(\sigma + it)\right\rVert \le C (\log|t|)^9$ for all $|t| > 3$ and $\sigma \ge 1 - A/(\log|t|)^9$, i.e. a quantitative bound on the logarithmic derivative of $\zeta$ in a Korobov–Vinogradov-shaped zero-free region.
--
--   - `LogDerivZetaIsHoloSmall σ₂` — the proposition that $\zeta'/\zeta$ is holomorphic on the punctured rectangle $([\sigma_2, 2] \times i[-3,3]) \setminus \{1\}$, controlling the low-height part of the contour.
--
--   **Downstream use.** The main PNT argument shows $\psi_\epsilon(X)$ equals the residue contribution $X \cdot \mathcal{M}(\widetilde{1_\epsilon})(1)$ from the pole at $s=1$ plus the sum of the pieces $I_1,\dots,I_9$, bounds each piece using the two zeta hypotheses above, and then unsmooths ($\epsilon \to 0$) to obtain $\psi(X) = X + O(X\exp(-c(\log X)^{1/10}))$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MediumPNT.lean (definitions vendored from this file)

import Mathlib.Algebra.Group.Support
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Chebyshev
import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Notation.Support
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_MellinCalculus_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Set Function Filter Complex Real

open ArithmeticFunction (vonMangoldt)
open scoped Chebyshev

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

namespace Chebyshev


end Chebyshev


noncomputable abbrev SmoothedChebyshevIntegrand
    (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ → ℂ :=
  fun s ↦ (- deriv riemannZeta s) / riemannZeta s *
    𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) s * (X : ℂ) ^ s

noncomputable def SmoothedChebyshev (SmoothingF : ℝ → ℝ) (ε : ℝ) (X : ℝ) : ℂ :=
  VerticalIntegral' (SmoothedChebyshevIntegrand SmoothingF ε X) ((1 : ℝ) + (Real.log X)⁻¹)

open ComplexConjugate


open MeasureTheory


-- TODO: add to mathlib
attribute [fun_prop] Continuous.const_cpow


--open scoped ArithmeticFunction in


noncomputable def I₁ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₂ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - T * I)))

noncomputable def I₃₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₈ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₁..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + T * I)))

noncomputable def I₉ (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

noncomputable def I₃ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..(-3),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₇ (SmoothingF : ℝ → ℝ) (ε T X σ₁ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (3 : ℝ)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₁ + t * I)))

noncomputable def I₄ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ - 3 * I)))

noncomputable def I₆ (SmoothingF : ℝ → ℝ) (ε X σ₁ σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ in σ₂..σ₁,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ + 3 * I)))

noncomputable def I₅ (SmoothingF : ℝ → ℝ) (ε X σ₂ : ℝ) : ℂ :=
  (1 / (2 * π * I)) *
    (I * (∫ t in (-3)..3, SmoothedChebyshevIntegrand SmoothingF ε X (σ₂ + t * I)))


def LogDerivZetaHasBound (A C : ℝ) : Prop := ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Ici (1 - A / Real.log |t| ^ 9)), ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤
    C * Real.log |t| ^ 9

def LogDerivZetaIsHoloSmall (σ₂ : ℝ) : Prop :=
    HolomorphicOn (fun (s : ℂ) ↦ ζ' s / (ζ s))
    (((uIcc σ₂ 2)  ×ℂ (uIcc (-3) 3)) \ {1})


-- TODO : Move elsewhere (should be in Mathlib!) NOT NEEDED


open Filter Topology

-- `x * rexp (-c * (log x) ^ B)) = Real.exp (Real.log x - c * (Real.log x) ^ B))`
-- so if `B < 1`, the exponent goes to infinity


