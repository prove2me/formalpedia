-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter25_chapter25_measure_theoretic_short
-- name    : ProofsInTheBook.Chapter25.chapter25_measure_theoretic_short
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-12T16:41:32.049491+00:00
-- url     : https://prove2.me/theorems/21da2a39-c3fb-4c5f-9fec-2b561e069320
-- title:
--   Buffon’s short-needle formula
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a measure space, let $d>0$, and let $B:\Omega\to\mathbb R^2$ be measurable with uniform distribution on $[-d/2,d/2]\times[0,\pi]$ with respect to $\mu$. Write $B(\omega)=(X(\omega),\Theta(\omega))$. For a real parameter l, let $N_l(\omega)$ equal 1 if
--   $$0\in[X(\omega)-l\sin\Theta(\omega)/2,\ X(\omega)+l\sin\Theta(\omega)/2],$$
--   and equal 0 otherwise. The angle is measured from the vertical axis. Assume in addition $0<l\le d$. Then
--   $$\int_\Omega N_l\,d\mu=\frac{2l}{d\pi}.$$
--   The expected value is taken with respect to the given measure, and uniformity on the rectangle is an explicit assumption.
-- source:
--   Repository endpoint: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter25.lean#L293. Archive authors: Enrico Z. Borba; Apache 2.0 license retained. The proof used by this endpoint comes from Mathlib Archive at commit c5ea00351c28e24afc9f0f84379aa41082b1188f. Topic: Aigner and Ziegler, Proofs from THE BOOK, 6th edition, Chapter 27, “Buffon’s needle problem”, pp. 189–192 (https://doi.org/10.1007/978-3-662-57265-8_27).

import Init
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Density
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Notation
import Mathlib
import Definitions.Def_P2MAssembly_Chapter25
open ProofsInTheBook.Chapter25
open scoped BigOperators
open MeasureTheory ProbabilityTheory Real

theorem ProofsInTheBook.Chapter25.chapter25_measure_theoretic_short {Ω : Type*} [MeasureSpace Ω]
    (d l : ℝ) (hd : 0 < d) (hl : 0 < l)
    (B : Ω → ℝ × ℝ) (hBₘ : Measurable B)
    (hB : MeasureTheory.pdf.IsUniform B
      ((Set.Icc (-d / 2) (d / 2)) ×ˢ (Set.Icc 0 π)) ℙ)
    (h : l ≤ d) :
    ℙ[BuffonsNeedle.N l B] = (2 * l) * (d * π)⁻¹ := by sorry
