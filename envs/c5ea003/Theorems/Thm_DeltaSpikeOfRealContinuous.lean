-- Prove2me | Theorems.Thm_DeltaSpikeOfRealContinuous
-- name    : DeltaSpikeOfRealContinuous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T14:58:32.749281+00:00
-- url     : https://prove2.me/theorems/1caa95ec-2a8d-44e0-8ab3-4e340d579785
-- title:
--   Continuity of the complex-valued delta spike $x \mapsto (\nu(x^{1/\varepsilon})/\varepsilon : \mathbb{C})$
-- statement:
--   Let $\nu : \mathbb{R} \to \mathbb{R}$ be of class $C^1$ and let $\varepsilon > 0$. Then the delta spike composed with the embedding $\mathbb{R} \hookrightarrow \mathbb{C}$,
--   $$x \;\longmapsto\; \Big(\mathrm{DeltaSpike}_{\nu,\varepsilon}(x) : \mathbb{C}\Big), \qquad \mathrm{DeltaSpike}_{\nu,\varepsilon}(x) = \frac{1}{\varepsilon}\,\nu\!\big(x^{1/\varepsilon}\big),$$
--   is continuous as a map $\mathbb{R} \to \mathbb{C}$.
--
--   This is the real-continuity statement for the spike upgraded through the continuous coercion into $\mathbb{C}$; it is the form actually needed when the spike appears as an integrand in complex-valued Mellin integrals.
--
--   In the PNT+ Mellin calculus, integrands such as $x \mapsto \mathrm{DeltaSpike}_{\nu,\varepsilon}(x)\, x^{s-1}$ must be shown measurable/continuous as complex-valued functions before their Mellin transforms and contour-shift identities can be established; this lemma supplies that ingredient.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/MellinCalculus.lean#L495-L497

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

theorem DeltaSpikeOfRealContinuous {ν : ℝ → ℝ} {ε : ℝ} (εpos : 0 < ε)
    (diffν : ContDiff ℝ 1 ν) : Continuous (fun x ↦ (DeltaSpike ν ε x : ℂ)) := by sorry
