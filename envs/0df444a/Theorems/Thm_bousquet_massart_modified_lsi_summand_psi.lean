-- Prove2me | Theorems.Thm_bousquet_massart_modified_lsi_summand_psi
-- name    : bousquet_massart_modified_lsi_summand_psi
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-24T04:57:47.296821+00:00
-- url     : https://prove2.me/theorems/bef8fb4b-2dc0-40f2-935d-ac98403f6a78
-- title:
--   Massart eq. (4): the modified log-Sobolev summand, single fibre
-- statement:
--   **Massart eq (4) — modified logarithmic Sobolev summand (single-fiber, ψ-form).** For a probability measure $\mu$ (one conditional fiber of the entropy tensorization), a measurable $Z$ with $e^{\lambda Z}$ and $\lambda Z e^{\lambda Z}$ integrable, and a constant reference exponent $c$ (the leave-one-out value $Z_k$, which is $\sigma(\text{coords}\neq k)$-measurable hence constant on the $k$-fiber), the entropy functional of $e^{\lambda Z}$ is bounded by the ψ-summand:
--
--   $$\lambda\,\mathbb{E}[Z e^{\lambda Z}] - \mathbb{E}[e^{\lambda Z}]\log \mathbb{E}[e^{\lambda Z}] \le \mathbb{E}\big[e^{\lambda Z}\,\psi(\lambda(Z-c))\big],\qquad \psi(x)=e^{-x}-1+x.$$
--
--   This is the per-coordinate conditional modified-LSI brick (BLM Theorem 6.6 / Massart's lemma). Summed over the coordinates $k$ against the sub-additivity (Han) tensorization of entropy applied to $e^{\lambda Z}$, it yields the full Massart eq (4) modified log-Sobolev inequality, which — with Bousquet's eq (6) per-summand bound and condition (3) — gives the differential inequality $G'' \le v\,e^{\lambda}$ integrated by the Herbst step to the sub-gamma cgf bound. Proof: the constant-reference variational (dual) bound of entropy $\mathrm{Ent}_\mu(Y)\le\int(Y\log Y - Y\log u-(Y-u))$ at $Y=e^{\lambda Z}$, $u=e^{\lambda c}>0$, followed by the pointwise identity $e^{a}(a-b)-(e^{a}-e^{b})=e^{a}(e^{b-a}-(b-a)-1)=e^{a}\psi(a-b)$. Here $\psi$ is written inline as $e^{-x}-1+x$ (= BLM's $\varphi(-x)$, $\varphi(x)=e^{x}-x-1$).
-- source:
--   Massart 2000, Ann. Probab. 28(2):863-884; Bousquet 2002, C.R.Acad.Sci.Paris 334:495-500, Lemma 3.1 eq (4); Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Theorem 6.6.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
open Real MeasureTheory

theorem bousquet_massart_modified_lsi_summand_psi
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    [IsProbabilityMeasure μ] {Z : α → ℝ} {lam c : ℝ}
    (hexp_int : Integrable (fun ω ↦ Real.exp (lam * Z ω)) μ)
    (hZexp_int : Integrable (fun ω ↦ lam * Z ω * Real.exp (lam * Z ω)) μ) :
    lam * (∫ ω, Z ω * Real.exp (lam * Z ω) ∂μ)
        - (∫ ω, Real.exp (lam * Z ω) ∂μ) * Real.log (∫ ω, Real.exp (lam * Z ω) ∂μ)
      ≤ ∫ ω, Real.exp (lam * Z ω)
            * (Real.exp (-(lam * (Z ω - c))) - 1 + lam * (Z ω - c)) ∂μ := by sorry
