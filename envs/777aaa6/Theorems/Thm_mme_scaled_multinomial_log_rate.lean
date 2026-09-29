-- Prove2me | Theorems.Thm_mme_scaled_multinomial_log_rate
-- name    : mme_scaled_multinomial_log_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T20:41:17.318363+00:00
-- url     : https://prove2.me/theorems/5cbf95cd-086d-4c9f-9eda-68b3c894b676
-- title:
--   Scaled multinomial counts have their exact logarithmic entropy rate
-- statement:
--   Let $C$ be a finite set and let $a_c\in\mathbb N$ be fixed counts. Put $A=\sum_{c\in C}a_c$ and, for each integer $m\geq0$, define the multinomial count
--   $$
--   Q_m=\binom{Am}{(a_cm)_{c\in C}}
--   =\frac{(Am)!}{\prod_{c\in C}(a_cm)!}.
--   $$
--   Then
--   $$
--   \lim_{m\to\infty}\frac{\log Q_m}{m}
--   =A\log A-\sum_{c\in C}a_c\log a_c.
--   $$
--   All logarithms are natural, and $0\log0$ is interpreted as $0$. Individual zero counts, the zero-total case, and the empty alphabet are included; no positivity assumption on the count vector is required.
--
--   This supplies the actual asymptotic exponential rate of a fixed joint-type class. The limit is proved from multinomial estimates, not assumed as an entropy hypothesis. It does not by itself bound competing joint types, choose a hash modulus, or establish a tensor value.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 3.6 Lemma 3.4 (multinomial entropy asymptotics) and Section 3.7 (joint and marginal index-sequence distributions), https://arxiv.org/html/2210.10173v5#S3.SS6 . Exact natural-log, denominator-cleared finite-alphabet formulation; zero counts and zero total included. Proof uses the accepted explicit two-sided regional multinomial estimate mme_regional_dependent_profile_entropy_bounds (3e9ba49e-f426-4a5a-8739-07e31d73eeb0) and derives the limit rather than assuming it.

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

open BigOperators Filter
open scoped Topology Classical
set_option autoImplicit false

theorem mme_scaled_multinomial_log_rate {C : Type*} [Fintype C] (a : C → ℕ) :
    Tendsto (fun m : ℕ ↦
        Real.log (Nat.multinomial Finset.univ (fun c ↦ a c * m) : ℝ) / (m : ℝ))
      atTop (𝓝 (((∑ c, a c : ℕ) : ℝ) * Real.log ((∑ c, a c : ℕ) : ℝ) -
        ∑ c, (a c : ℝ) * Real.log (a c : ℝ))) := by sorry
