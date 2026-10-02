-- Prove2me | Theorems.Thm_BuffonsNeedle_buffon_integral
-- name    : BuffonsNeedle.buffon_integral
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:41:28.587311+00:00
-- url     : https://prove2.me/theorems/d72892c8-d89e-4523-b791-91a04075b2cf
-- title:
--   A double-integral formula for the needle crossing indicator
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a measure space, let $d>0$, and let $B:\Omega\to\mathbb R^2$ be measurable with uniform distribution on $[-d/2,d/2]\times[0,\pi]$ with respect to $\mu$. Write $B(\omega)=(X(\omega),\Theta(\omega))$. For a real parameter l, let $N_l(\omega)$ equal 1 if
--   $$0\in[X(\omega)-l\sin\Theta(\omega)/2,\ X(\omega)+l\sin\Theta(\omega)/2],$$
--   and equal 0 otherwise. The angle is measured from the vertical axis. Then
--   $$\int_\Omega N_l\,d\mu=\frac1{d\pi}\int_{\theta\in[0,\pi]}\int_{x\in[-d/2,d/2]\cap[-l\sin\theta/2,l\sin\theta/2]}1\,dx\,d\theta.$$
--   The integrals on the right use Lebesgue measure. This intermediate identity permits arbitrary real l; positivity and the short-needle restriction are not hypotheses.
-- source:
--   Mathlib Archive original proof: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Archive/Wiedijk100Theorems/BuffonsNeedle.lean#L193. Archive authors: Enrico Z. Borba; Apache 2.0 license retained. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 27, “Buffon’s needle problem”, pp. 189–192 (https://doi.org/10.1007/978-3-662-57265-8_27).

import Init
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Notation
import Mathlib
import Definitions.Def_P2MAssembly_Chapter25
open MeasureTheory (MeasureSpace IsProbabilityMeasure Measure pdf.IsUniform)
open ProbabilityTheory Real
open BuffonsNeedle
variable
  /- Probability theory variables. -/
  {Ω : Type*} [MeasureSpace Ω]
  /- Buffon's needle variables. -/
  /-
    - `d > 0` is the distance between parallel lines.
    - `l > 0` is the length of the needle.
  -/
  (d l : ℝ)
  (hd : 0 < d)
  (hl : 0 < l)
  /- `B = (X, Θ)` is the joint random variable for the x-position and angle of the needle. -/
  (B : Ω → ℝ × ℝ)
  (hBₘ : Measurable B)
  /- `B` is uniformly distributed on `[-d/2, d/2] × [0, π]`. -/
  (hB : pdf.IsUniform B ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) ℙ)
include hd hB hBₘ

lemma BuffonsNeedle.buffon_integral :
    𝔼[N l B] = (d * π)⁻¹ *
      ∫ (θ : ℝ) in Set.Icc 0 π,
      ∫ (_ : ℝ) in Set.Icc (-d / 2) (d / 2) ∩ Set.Icc (-θ.sin * l / 2) (θ.sin * l / 2), 1 := by sorry
