-- Prove2me | Theorems.Thm_tendsto_S_S_zero
-- name    : tendsto_S_S_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:22:13.980791+00:00
-- url     : https://prove2.me/theorems/b0812dc7-100d-4115-ace9-de14e96e97fb
-- title:
--   tendsto S S zero: tendsto S S zero
-- statement:
--   The tendsto S S zero construction uses the tendsto S S zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L2029-L2046
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/upstream-config/patches/PrimeNumberTheoremAnd-lean4341.patch#L2029-L2046

import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Lemmas
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
import Definitions.Def_PrimeNumberTheoremAnd_SmoothExistence
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Definitions.Def_PrimeNumberTheoremAnd_Wiener
set_option autoImplicit true
open Real BigOperators ArithmeticFunction MeasureTheory Filter Set FourierTransform LSeries
  Asymptotics SchwartzMap
open Complex hiding log
open scoped Topology
open scoped ContDiff
open scoped ComplexConjugate
variable {n : ℕ} {A a b c d u x y t σ' : ℝ} {ψ Ψ : ℝ → ℂ} {F G : ℂ → ℂ} {f : ℕ → ℂ} {𝕜 : Type}
  [RCLike 𝕜]
attribute [fun_prop] Real.continuous_fourierChar
attribute [fun_prop] measurable_coe_nnreal_ennreal
attribute [local instance] _p2m_local_instance_2ee1fa6ce2_1687

theorem tendsto_S_S_zero {f : ℕ → ℝ} (hpos : 0 ≤ f)
    (hcheby : (∃ C : ℝ, ∀ n : ℕ, cumsum (fun k : ℕ ↦ ‖(f k : ℂ)‖) n ≤ C * n)) :
    TendstoUniformlyOnFilter (S f) (S f 0) (𝓝[>] 0) atTop := by sorry
