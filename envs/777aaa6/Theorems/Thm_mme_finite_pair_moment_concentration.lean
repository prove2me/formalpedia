-- Prove2me | Theorems.Thm_mme_finite_pair_moment_concentration
-- name    : mme_finite_pair_moment_concentration
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T16:30:28.194587+00:00
-- url     : https://prove2.me/theorems/c8305cf1-7f4b-4d22-ae52-87cf6ebddeb5
-- title:
--   Second-moment tail bound from approximate pair moments
-- statement:
--   A finite uniform family of [0,1]-valued variables with first-moment error at most 4/m and distinct-pair moment error at most 16/m has empirical-average squared-tail probability at most 25/(m epsilon squared), provided its variable count is at least m. A supporting second-moment lemma; the physical histogram application separately derives these moment conditions.
-- source:
--   Quantitative finite realization for a jointly processed constituent region, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_finite_pair_moment_concentration {U T : Type*} [Fintype U] [Nonempty U] [Fintype T]
    (Z : T → U → ℝ) (a : T → ℝ) (m eps : ℝ)
    (hm : 0 < m) (hmn : m ≤ Fintype.card T) (heps : 0 < eps)
    (hZ : ∀ t f, 0 ≤ Z t f ∧ Z t f ≤ 1) (ha : ∀ t, 0 ≤ a t ∧ a t ≤ 1)
    (hfirst : ∀ t, |(𝔼 f, Z t f) - a t| ≤ 4 / m)
    (hsecond : ∀ t s, t ≠ s → |(𝔼 f, Z t f * Z s f) - a t * a s| ≤ 16 / m) :
    (𝔼 f : U, if eps ≤ |((∑ t, Z t f) - ∑ t, a t) / Fintype.card T| then (1 : ℝ) else 0) ≤
      25 / (m * eps ^ 2) := by sorry
