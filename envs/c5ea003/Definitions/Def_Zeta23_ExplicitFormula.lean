-- Prove2me | Definitions.Def_Zeta23_ExplicitFormula
-- name    : Zeta23_ExplicitFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:03:23.053184+00:00
-- url     : https://prove2.me/theorems/62a4076b-d9f3-4104-9ed8-bd52bbc704e9
-- title:
--   Weil explicit formula: literature form and Appendix A vocabulary
-- statement:
--   This bundle defines the vocabulary of the project's explicit-formula bridge (`Zeta23/ExplicitFormula.lean`), which derives the paper's normalisation of Weil's explicit formula (H-EF, [prop:EF]) from the literature form [eq:EFstd], following the paper's Appendix A.
--
--   Central definitions: **`literatureRHS`** is the right-hand side of [eq:EFstd], verbatim:
--   $$h(i/2) + h(-i/2) - \sum_{n \ge 1}\frac{\Lambda(n)}{\sqrt n}\bigl(k(\log n) + k(-\log n)\bigr) + \frac{1}{2\pi}\int_{\mathbb{R}} h(r)\Bigl[\mathrm{Re}\,\frac{\Gamma'}{\Gamma}\Bigl(\frac14 + \frac{ir}{2}\Bigr) - \log\pi\Bigr]dr,$$
--   with $h := $ `paperFT` $k$ (the $n$-sum is written over all $n : \mathbb{N}$; since $\Lambda(0) = \Lambda(1) = 0$ and $k$ is compactly supported it has finite support). **`EF_lit`** is the literature form of the explicit formula as a proposition: for every $k \in C_c^2(\mathbb{R})$ with $h(z) := \int k(u)e^{izu}du$, the zero sum $\sum_\rho m_\rho h(\gamma_\rho)$ converges absolutely and equals `literatureRHS k` ([IK04, Thm 5.12] specialised to $\zeta$ / [Wei52] / [Bom00]); in the project it is a hypothesis (a structure field in `Hypotheses.lean`), never a Lean axiom. **`gammaBracket`** is the archimedean bracket $\mathrm{Re}\,\frac{\Gamma'}{\Gamma}(\frac14 + \frac{ir}{2}) - \log\pi$ (equal to $2\pi\mu(r)$ by [eq:mudef]), spelled via `Complex.digamma`.
--
--   Helpers for the Appendix A convolution argument: **`tilde`** $\tilde g(u) := \overline{g(-u)}$; **`weilTest`** $k := f \star \tilde g$, the Weil test function built by Mathlib convolution; and **`EL`**, the truncated growing weight $E_L(u) := \mathbf{1}_{[-L,L]}(u)\,e^{|u|/2}$ used in the convergence estimates.
--
--   The module proves (literature form) $\Rightarrow$ `ExplicitFormulaPaper` — i.e. $W(f,g) = \int_{\mathbb{R}} h_f(\tau)\overline{h_g(\tau)}\,\nu_X(\tau)\,d\tau$ for supported $f, g$ — which is the H-EF input every headline theorem consumes.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ExplicitFormula.lean, docstring tag [eq:EFstd]

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

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ExplicitFormula.lean  —  the explicit formula, normalisations (paper App. A [app:EF]).

The *normalisation chain*: the passage from a literature-verbatim explicit formula to the paper's
density ν_X = μ + Π_X + P_X [eq:mudef]–[eq:nudef], with every 2π and every sign:

  * `EF.literatureRHS` / `EF_lit` : the right-hand side of [eq:EFstd] (App. A, first display), i.e. the
    Weil explicit formula in the form the paper quotes from [IK04, Thm 5.12] / [Wei52] / [Bom00],
    for a single test function k ∈ C_c²(ℝ) with h(z) := ∫ k(u) e^{izu} du;
  * `EF.prop_EF_of_lit` : [eq:EFstd] for k := f ⋆ g̃  ⟹  [eq:EF]  W(f,g) = ∫ h_f(τ) conj(h_g(τ)) ν_X(τ) dτ,
    X = e^L, for f, g ∈ C_c²(ℝ) supported in [−L/2, L/2]  — exactly App. A's three identifications
    (Gamma term, prime term, pole term) plus h_{f⋆g̃}(z) = h_f(z)·conj(h_g(conj z)).

The truth of [eq:EFstd] itself (contour integration of
h((s-1/2)/i)·ξ'/ξ(s)) is the hypothesis `EF_lit`, stated for the zero configuration
abstractly.

CONVENTIONS (paper [Notation]).  Paper Fourier transform:
    f̂(τ) = h_f(τ) := ∫_ℝ f(u) e^{iτu} du,   inversion  f(u) = (1/2π) ∫_ℝ h_f(r) e^{-iru} dr.
Mathlib: 𝓕 f w = ∫ v, exp(-2πi v w) • f v.  Dictionary (proved below, `paperFT_ofReal_eq_fourier`):
    h_f(τ) = 𝓕 f (-τ/(2π)).
-/

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23
namespace EF

/-! ### App. A objects owned by this file -/

/-- App. A: `g̃(u) := conj (g(−u))`. -/
def tilde (g : ℝ → ℂ) : ℝ → ℂ := fun u => conj (g (-u))

/-- App. A: the Weil test function `k := f ⋆ g̃`, i.e. `k(x) = ∫ f(t) g̃(x − t) dt`
(Mathlib convolution w.r.t. Lebesgue measure and the ℝ-bilinear map `ContinuousLinearMap.mul ℝ ℂ`). -/
def weilTest (f g : ℝ → ℂ) : ℝ → ℂ := f ⋆[ContinuousLinearMap.mul ℝ ℂ] tilde g

end EF


namespace EF

/-! ## The literature form [eq:EFstd] -/

/-- The Gamma-factor bracket in [eq:EFstd]: `Re Γ'/Γ(1/4 + ir/2) − log π`
( = Γ_ℝ'/Γ_ℝ(1/2+ir) + Γ_ℝ'/Γ_ℝ(1/2−ir), Γ_ℝ(s) = π^{-s/2}Γ(s/2); equals 2π μ(r) by [eq:mudef]).
Γ'/Γ is spelled `Complex.digamma` (= logDeriv Gamma), identically to `Zeta23.mu` in Defs.lean. -/
def gammaBracket (r : ℝ) : ℝ := (Complex.digamma (1 / 4 + I * r / 2)).re - Real.log π

/-- Right-hand side of [eq:EFstd] (App. A, first display), VERBATIM:
`h(i/2) + h(−i/2) − Σ_{n≥1} Λ(n) n^{-1/2} (k(log n) + k(−log n)) + (1/2π) ∫_ℝ h(r) [Re Γ'/Γ(1/4 + ir/2) − log π] dr`
with `h := paperFT k`.  The n-sum is written over all `n : ℕ` (Λ(0) = Λ(1) = 0); for compactly supported k it
has finite support. -/
def literatureRHS (k : ℝ → ℂ) : ℂ :=
  paperFT k (I / 2) + paperFT k (-I / 2)
  - ∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ)
      * (k (Real.log n) + k (-Real.log n))
  + (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (gammaBracket r : ℂ)

/-- **H-EF, literature form** ([eq:EFstd]; [IK04, Thm 5.12] specialised to ζ / [Wei52] / [Bom00]):
for every `k ∈ C_c²(ℝ)` with `h(z) := ∫ k(u)e^{izu}du`,
`Σ_ρ m_ρ h(γ_ρ) = literatureRHS k`, the zero sum converging absolutely (paper: "here absolutely
convergent since h(r) ≪_k (1+|r|)^{-2} on |Im r| ≤ 1/2").  It is a hypothesis
(structure field in Hypotheses.lean), never a Lean axiom. -/
def EF_lit (Z : ZeroConfig) : Prop :=
  ∀ k : ℝ → ℂ, ContDiff ℝ 2 k → HasCompactSupport k →
    Summable (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ)) ∧
    ∑' ρ : Z.carrier, (Z.mult ρ : ℂ) * paperFT k (gammaOf ρ) = literatureRHS k


/-! ## ℂ-specialised integral helpers

(In this toolchain `rw [← integral_const_mul]` fails to key-match on ℂ-valued integrals because the
RCLike-generic lemma elaborates `Mul ℂ`/`NormedAddCommGroup ℂ` through a different instance path than
a goal written with `*`; restating the lemmas at ℂ (proved by `exact`) makes `rw` usable.) -/




/-! ## Dictionary with Mathlib's Fourier transform -/




/-! ## The test function k = f ⋆ g̃ -/










/-! ## App. A: the three identifications -/








/-! ### Pole term: inversion + Fubini, and the two explicit integrals -/











/-- The truncated growing weight `E_L(u) := 1_{[−L,L]}(u) e^{|u|/2}`. -/
def EL (L : ℝ) : ℝ → ℂ := (Icc (-L) L).indicator fun u => (Real.exp (|u| / 2) : ℂ)





/-! ### Integrability of the three densities against h (from the computations above) -/





/-! ## Adding up -/


/-! ## [prop:EF] from the literature form -/


end EF
end Zeta23


