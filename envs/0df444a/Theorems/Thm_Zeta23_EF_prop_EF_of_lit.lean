-- Prove2me | Theorems.Thm_Zeta23_EF_prop_EF_of_lit
-- name    : Zeta23.EF.prop_EF_of_lit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:48:28.310868+00:00
-- url     : https://prove2.me/theorems/aea29207-e56f-4f2f-9867-fd003221b3ee
-- title:
--   From the literature explicit formula [eq:EFstd] to the paper's form [eq:EF]: $W(f,g) = \int h_f\,\overline{h_g}\,\nu_X$
-- statement:
--   Let $Z$ be an abstract zero configuration (a set of distinct points $\rho$ in the strip $0 \le \operatorname{Re}\rho \le 1$ with multiplicities $m_\rho \ge 1$, locally finite in the ordinate and invariant under $\rho \mapsto 1-\bar\rho$), and assume the hypothesis `EF_lit Z` — the literature (Weil) explicit formula [eq:EFstd]: for every $k \in C_c^2(\mathbb{R})$, with $h(z) = \int k(u)e^{izu}\,du$, the zero sum $\sum_\rho m_\rho\, h(\gamma_\rho)$ (over $\rho \in Z$, $\gamma_\rho = (\rho-\tfrac12)/i$) converges and equals $h(i/2)+h(-i/2) - \sum_n \Lambda(n)n^{-1/2}(k(\log n)+k(-\log n)) + \frac{1}{2\pi}\int h(r)\,[\operatorname{Re}\frac{\Gamma'}{\Gamma}(\tfrac14+\tfrac{ir}{2}) - \log\pi]\,dr$.
--
--   Let $L > 0$ and let $f, g \in C^2(\mathbb{R},\mathbb{C})$ have closed supports contained in $[-L/2, L/2]$. Assume the two integrability side conditions that Appendix A uses silently for $k = f \star \tilde{g}$ (where $\tilde{g}(u) = \overline{g(-u)}$): the Fourier transform $\mathcal{F}(f \star \tilde g)$ is integrable, and $\tau \mapsto h_{f\star\tilde g}(\tau)\,\mu(\tau)$ is integrable (both follow from [eq:hfbound] and [eq:mufacts]). Then, with $X = e^{L}$ and $\nu_X = \mu + \Pi_X + P_X$ the paper's density [eq:nudef]:
--
--   1. the Weil sum $W(f,g) = \sum_{\rho} m_\rho\, h_f(\gamma_\rho)\,\overline{h_g(\overline{\gamma_\rho})}$ is summable over the zeros of $Z$;
--   2. $\tau \mapsto h_f(\tau)\,\overline{h_g(\tau)}\,\nu_X(\tau)$ is integrable on $\mathbb{R}$; and
--
--   $$W(f,g) \;=\; \int_{\mathbb{R}} h_f(\tau)\,\overline{h_g(\tau)}\,\nu_X(\tau)\,d\tau.$$
--
--   **Role.** This is the main theorem of the normalization chain in `Zeta23.ExplicitFormula`: it combines the Gamma-term, prime-term and pole-term identifications for $k = f \star \tilde g$ with the factorization $h_{f\star\tilde g}(z) = h_f(z)\,\overline{h_g(\bar z)}$, turning [eq:EFstd] into the paper's Proposition [prop:EF]. It feeds `Zeta23.EF.explicitFormulaPaper_of_lit`, the packaged form consumed by the rest of the project.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean#L699-L731, docstring tags [eq:EFstd], [eq:EF]

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

theorem Zeta23.EF.prop_EF_of_lit (Z : ZeroConfig) (hEF : EF_lit Z) {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2))
    (hFk : Integrable (𝓕 (weilTest f g)))
    (hμ : Integrable (fun τ : ℝ => paperFT (weilTest f g) τ * (mu τ : ℂ))) :
    Summable (fun ρ : Z.carrier => Z.Wsummand f g ρ) ∧
    Integrable (fun τ : ℝ => paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ)) ∧
    Z.W f g = ∫ τ : ℝ, paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ) := by sorry
