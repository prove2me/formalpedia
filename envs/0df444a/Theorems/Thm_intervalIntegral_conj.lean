-- Prove2me | Theorems.Thm_intervalIntegral_conj
-- name    : intervalIntegral_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:07:53.213536+00:00
-- url     : https://prove2.me/theorems/787f6253-85ef-439d-8894-967dcf1ef4dd
-- title:
--   Complex conjugation commutes with the interval integral: $\int_a^b \overline{f} = \overline{\int_a^b f}$
-- statement:
--   Let $f : \mathbb{R} \to \mathbb{C}$ and let $a, b \in \mathbb{R}$. Then
--
--   $$\int_{a}^{b} \overline{f(x)} \, dx \;=\; \overline{\int_{a}^{b} f(x) \, dx},$$
--
--   where $\overline{\,\cdot\,}$ denotes complex conjugation and the integrals are interval (oriented) integrals. No integrability hypothesis is needed: if $f$ is not interval-integrable then neither is $\overline f$, and both sides are $0$ by convention.
--
--   This lemma supports the conjugation-symmetry arguments for the zeta function (the reflection $\zeta(\overline{s}) = \overline{\zeta(s)}$ and its consequences for $\zeta_0$ and $\zeta'$): integral representations of $\zeta$ at the conjugated point are identified with conjugates of the original integrals, allowing bounds proved in the upper half-plane to transfer to the lower half-plane for free.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaConj.lean#L81-L84

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open scoped Complex ComplexConjugate
set_option backward.isDefEq.respectTransparency false

theorem intervalIntegral_conj {f : ℝ → ℂ} {a b : ℝ} :
    ∫ (x : ℝ) in a..b, conj (f x) = conj (∫ (x : ℝ) in a..b, f x) := by sorry
