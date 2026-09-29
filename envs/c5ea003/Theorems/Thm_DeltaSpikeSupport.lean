-- Prove2me | Theorems.Thm_DeltaSpikeSupport
-- name    : DeltaSpikeSupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:59:02.249157+00:00
-- url     : https://prove2.me/theorems/09c9d01c-980e-458e-8967-1fb36a7659b5
-- title:
--   The delta spike vanishes outside $[2^{-\varepsilon}, 2^{\varepsilon}]$
-- statement:
--   Let $\nu : \mathbb{R} \to \mathbb{R}$ have support contained in the interval $[1/2, 2]$, let $\varepsilon > 0$, and let $x \ge 0$. If $x$ lies outside the interval $[2^{-\varepsilon}, 2^{\varepsilon}]$, then the delta spike vanishes there:
--   $$x \notin \big[2^{-\varepsilon},\, 2^{\varepsilon}\big] \;\Longrightarrow\; \mathrm{DeltaSpike}_{\nu,\varepsilon}(x) = \frac{1}{\varepsilon}\,\nu\!\big(x^{1/\varepsilon}\big) = 0.$$
--
--   The point is the change of scale: $x^{1/\varepsilon} \in [1/2, 2]$ exactly when $x \in [2^{-\varepsilon}, 2^{\varepsilon}]$, so outside this window the argument of $\nu$ escapes its support.
--
--   This support control shows that the spike concentrates at $x = 1$ as $\varepsilon \to 0$, which is the mechanism by which the smoothed Chebyshev function $\psi_\varepsilon(X)$ approximates $\psi(X)$ with an error governed by the prime-power mass in the narrow window $[2^{-\varepsilon}X, 2^{\varepsilon}X]$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L484-L487

import Batteries.Tactic.Lemma
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.Bound
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Definitions.Def_MellinCalculus_defs

open scoped ContDiff

set_option lang.lemmaCmd true

-- TODO: move near `MeasureTheory.setIntegral_prod`

-- How to deal with this coercion?... Ans: (f ·)
--- noncomputable def funCoe (f : ℝ → ℝ) : ℝ → ℂ := fun x ↦ f x

open Complex Topology Filter Real MeasureTheory Set

variable {𝕂 : Type*} [RCLike 𝕂]

-- TODO: generalize to `RCLike`

local notation (name := mellintransform) "𝓜" => mellin

theorem DeltaSpikeSupport {ν : ℝ → ℝ} {ε x : ℝ} (εpos : 0 < ε) (xnonneg : 0 ≤ x)
    (suppν : ν.support ⊆ Icc (1 / 2) 2) :
    x ∉ Icc (2 ^ (-ε)) (2 ^ ε) → DeltaSpike ν ε x = 0 := by sorry
