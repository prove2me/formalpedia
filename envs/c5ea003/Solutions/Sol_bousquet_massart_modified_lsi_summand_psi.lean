-- Prove2me | solution 1 for bousquet_massart_modified_lsi_summand_psi
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-24T04:58:02.403867+00:00
-- url     : https://prove2.me/submissions/4250cbbf-c783-46f9-a47b-d3b374632ea7

import Theorems.Thm_EntVariational_ent_le_integral_sub_const_ref
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

open Real MeasureTheory

/-- **Per-coordinate / conditional Massart eq (4) summand (the modified-LSI brick).**
Massart 2000 (Ann. Probab. 28:863–884); Bousquet 2002 (C.R.Acad.Sci.Paris 334:495–500) Lemma 3.1
eq (4); BLM "Concentration Inequalities" (OUP 2013) Theorem 6.6.

For a probability measure `μ` (one conditional fiber), a measurable `Z` with `e^{λZ}` and
`λZe^{λZ}` integrable, and a fiberwise-constant reference exponent `c` (= the leave-one-out
`Z_k`, which is `σ(coords≠k)`-measurable hence constant on the `k`-fiber):

  `λ ∫ Z e^{λZ} − (∫ e^{λZ}) log(∫ e^{λZ})  ≤  ∫ e^{λZ(ω)} · ψ(λ(Z ω − c)) dμ`,  ψ(x)=e^{−x}−1+x.

The LHS is `Ent_μ(e^{λZ})` in eq (4)'s `λE[Ze^{λZ}]−E[e^{λZ}]logE[e^{λZ}]` form; the RHS
integrand is the modified-LSI summand `e^{λZ} ψ(λ(Z−c))`.  Proof = the Proved constant-reference
variational bound `EntVariational.ent_le_integral_sub_const_ref` at `Y = e^{λZ}`, `u = e^{λc}`,
then the pointwise Gibbs identity `e^a(a−b)−(e^a−e^b) = e^a(e^{b−a}−(b−a)−1) = e^a ψ(a−b)`. -/
theorem solution
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {Z : α → ℝ} {lam c : ℝ}
    (hexp_int : Integrable (fun ω ↦ Real.exp (lam * Z ω)) μ)
    (hZexp_int : Integrable (fun ω ↦ lam * Z ω * Real.exp (lam * Z ω)) μ) :
    lam * (∫ ω, Z ω * Real.exp (lam * Z ω) ∂μ)
        - (∫ ω, Real.exp (lam * Z ω) ∂μ) * Real.log (∫ ω, Real.exp (lam * Z ω) ∂μ)
      ≤ ∫ ω, Real.exp (lam * Z ω) * (Real.exp (-(lam * (Z ω - c))) - 1 + lam * (Z ω - c)) ∂μ := by
  set Y : α → ℝ := fun ω ↦ Real.exp (lam * Z ω) with hY
  set u : ℝ := Real.exp (lam * c) with hu
  have hu_pos : 0 < u := Real.exp_pos _
  have hY_nonneg : ∀ ω, 0 ≤ Y ω := fun ω ↦ (Real.exp_pos _).le
  have hY_int : Integrable Y μ := hexp_int
  have hYlog_eq : (fun ω ↦ Y ω * Real.log (Y ω))
      = fun ω ↦ lam * Z ω * Real.exp (lam * Z ω) := by
    funext ω; rw [hY]; rw [Real.log_exp]; ring
  have hYlog_int : Integrable (fun ω ↦ Y ω * Real.log (Y ω)) μ := by
    rw [hYlog_eq]; exact hZexp_int
  have hvar := EntVariational.ent_le_integral_sub_const_ref
    (μ := μ) (Y := Y) (u := u) hY_nonneg hY_int hYlog_int hu_pos
  -- LHS of hvar = eq(4)'s λE[Ze^{λZ}] − E[e^{λZ}]logE[e^{λZ}]
  have hLHS_eq : (∫ ω, Y ω * Real.log (Y ω) ∂μ) - (∫ ω, Y ω ∂μ) * Real.log (∫ ω, Y ω ∂μ)
      = lam * (∫ ω, Z ω * Real.exp (lam * Z ω) ∂μ)
        - (∫ ω, Real.exp (lam * Z ω) ∂μ) * Real.log (∫ ω, Real.exp (lam * Z ω) ∂μ) := by
    congr 1
    rw [hYlog_eq, ← integral_const_mul lam]
    apply integral_congr_ae; filter_upwards with ω; ring
  rw [hLHS_eq] at hvar
  refine le_trans hvar (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards with ω
  simp only [hY, hu, Real.log_exp]
  -- e^{λZω}(λZω) − e^{λZω}(λc) − (e^{λZω} − e^{λc}) = e^{λZω}·ψ(λ(Zω − c))
  -- key exponential identity: e^{λZω} · e^{-(λ(Zω−c))} = e^{λc}
  have hkey : Real.exp (lam * Z ω) * Real.exp (-(lam * (Z ω - c))) = Real.exp (lam * c) := by
    rw [← Real.exp_add]; congr 1; ring
  -- expand RHS and use hkey
  rw [mul_add, mul_sub, mul_one, hkey]
  ring
