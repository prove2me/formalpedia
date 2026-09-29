-- Prove2me | Theorems.Thm_modified_lsi_sup_functional_measure_pi
-- name    : modified_lsi_sup_functional_measure_pi
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-24T18:23:23.067142+00:00
-- url     : https://prove2.me/theorems/0210b4c0-aa9c-43cc-adf4-bf7ee9fe0908
-- statement:
--   Tensorized modified log-Sobolev inequality (Massart/Bousquet entropy-method core) for a real functional Z over a product measure Measure.pi with a leave-one-out family Z_k (Z_k coordinate-k-independent), bounded so c<=exp(lam Z)<=C (c>0) and |Z_k|<=Dzk: Ent_pi(exp(lam Z)) <= sum_k int exp(lam Z) * phi(-lam(Z - Z_k)) d(Measure.pi), phi(u)=e^u-1+u. This is the modified-LSI the sigma^2-aware Bennett/Bousquet concentration for suprema of empirical processes consumes. Reduction onto the positivity-restricted n-coordinate Han subadditivity (g=exp(lam Z)) plus the per-coordinate modified-LSI summand, folded via measurePreserving_piFinSuccAbove.
-- source:
--   Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013) Ch.6; Bousquet 2002 CRAS; Klein-Rio 2005 Ann. Probab. Thm 1.1(c); Massart modified log-Sobolev.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open Real MeasureTheory

theorem modified_lsi_sup_functional_measure_pi
    {n : ℕ} {α : Fin n → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
    (Z : (∀ i, α i) → ℝ) (Zk : Fin n → (∀ i, α i) → ℝ) (lam : ℝ)
    (hZmeas : Measurable Z) (hZkmeas : ∀ k, Measurable (Zk k))
    (hZk_indep : ∀ k x t, Zk k (Function.update x k t) = Zk k x)
    (c C Dzk : ℝ) (hcpos : 0 < c)
    (hglb : ∀ x, c ≤ Real.exp (lam * Z x))
    (hgub : ∀ x, Real.exp (lam * Z x) ≤ C)
    (hZkbd : ∀ k x, |Zk k x| ≤ Dzk) :
    (∫ x, Real.exp (lam * Z x) * Real.log (Real.exp (lam * Z x)) ∂(Measure.pi μ)
      - (∫ x, Real.exp (lam * Z x) ∂(Measure.pi μ))
          * Real.log (∫ x, Real.exp (lam * Z x) ∂(Measure.pi μ)))
    ≤ ∑ k : Fin n, ∫ x, Real.exp (lam * Z x)
        * (Real.exp (-(lam * (Z x - Zk k x))) - 1 + lam * (Z x - Zk k x)) ∂(Measure.pi μ) := by sorry
