-- Prove2me | Theorems.Thm_measure_Ici_toReal_continuous_of_atomless
-- name    : measure_Ici_toReal_continuous_of_atomless
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-04T01:38:53.253567+00:00
-- url     : https://prove2.me/theorems/953eb342-f5fe-482f-91d5-3c5a39ef982b
-- statement:
--   The tail function $p\mapsto\nu([p,\infty))$ of an atomless finite measure $\nu$ on $\mathbb R$ (i.e. $\nu\{p\}=0$ for every $p$) is continuous. This is the continuity of the complementary cdf of an atomless distribution; it supplies the continuity input for the existence and measurability of revenue-maximizing posted prices.
-- source:
--   Buying to Bundle: Optimal Sourcing from Monopolistic Sellers, Lemmas A.1/C.1 (Sec. 4 / App. C)

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

theorem measure_Ici_toReal_continuous_of_atomless
    (ν : Measure ℝ) [IsFiniteMeasure ν] (hatom : ∀ p : ℝ, ν {p} = 0) :
    Continuous fun p : ℝ => (ν (Ici p)).toReal := by sorry
