-- Prove2me | Theorems.Thm_Zeta23_EF_integrable_inversion_kernel
-- name    : Zeta23.EF.integrable_inversion_kernel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:46:58.604622+00:00
-- url     : https://prove2.me/theorems/c179a3f3-b6c1-4959-95d6-ae909e7bf8c2
-- title:
--   Joint integrability of the Fourier-inversion kernel $(u,\tau)\mapsto h_k(\tau)e^{-i\tau u}E(u)$
-- statement:
--   For a test function $k:\mathbb{R}\to\mathbb{C}$ write $h_k(z)=\int_{\mathbb{R}}k(u)e^{izu}\,du$ (`paperFT`), and let $\mathcal{F}k$ denote Mathlib's Fourier transform of $k$. Suppose $\mathcal{F}k$ is integrable and $E:\mathbb{R}\to\mathbb{C}$ is integrable. Then the two-variable kernel
--   $$(u,\tau)\;\longmapsto\;h_k(\tau)\,e^{-i\tau u}\,E(u)$$
--   is integrable on $\mathbb{R}^2$ with respect to the product Lebesgue measure (in Lean, the uncurried function is `Integrable` for `volume.prod volume`).
--
--   Since $|h_k(\tau)e^{-i\tau u}E(u)|=|h_k(\tau)|\,|E(u)|$, this is a Tonelli-type product bound (note $|h_k(\tau)|=|(\mathcal{F}k)(-\tau/2\pi)|$ up to the normalization relating `paperFT` to $\mathcal{F}$). The lemma licenses the Fubini swaps in the Appendix A computations that convert $\tau$-integrals against $h_k$ into $u$-integrals against $k$; it is consumed by `Zeta23.EF.integrable_paperFT_mul_PiX` and `Zeta23.EF.pole_term`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L374-L391

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction
set_option backward.isDefEq.respectTransparency false
open Zeta23
open EF

theorem Zeta23.EF.integrable_inversion_kernel {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) {E : ℝ → ℂ}
    (hE : Integrable E) :
    Integrable (Function.uncurry fun (u τ : ℝ) => paperFT k τ * cexp (-I * τ * u) * E u)
      (volume.prod volume) := by sorry
