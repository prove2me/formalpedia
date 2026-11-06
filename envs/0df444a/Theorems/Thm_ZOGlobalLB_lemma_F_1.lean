-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_F_1
-- name    : ZOGlobalLB.lemma_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:49:43.446198+00:00
-- url     : https://prove2.me/theorems/ff09f57e-b1a5-421a-a2b3-642cfce8f61a
-- title:
--   Lemma F.1 — uniform physical parameters and dimension conditions
-- statement:
--   There is a universal $C>0$ such that, whenever $\epsilon^2\le c_0B$ (with $c_0$ of (150)) and $d\ge C\frac{B}{\epsilon^2}\log\bigl(2+\frac{BL_0^2}{\epsilon^4}\bigr)$, the choice $T=\lfloor a_TB/\epsilon^2\rfloor$, $\sigma^2=a_\sigma L_0^2/\epsilon^2$, $r=\lfloor d/2\rfloor$, $m=d-r$, $s=m-T+1$, $\ell_0=\lfloor s^2\sigma^2/(2048m)\rfloor$, $N_0=\lfloor a_NdT\sigma^2\rfloor$ satisfies:
--
--   1. $T\ge8$, $T\le r$, $T\le m$, $\sigma^2\ge1$;
--   2. the smoothness, gap and sample budgets: $\lambda H_*/b^2=H$, $12\lambda T\le\Delta$, $\frac{\lambda}{b}(c_*\sqrt T+C_*+\sqrt{C_N}\sigma)\le L_0/2$;
--   3. the list conditions $s\ge72$, $\ell_0\ge1$, $\log\ell_0\le s/8$, and $N_0+1\le T\ell_0/4$;
--   4. the future-projection bound $p_{\mathrm{bad}}<1/12$, so that $2^{-T}+p_{\mathrm{bad}}+N_0^2/M\le11/48$ for every $M\ge12N_0^2$;
--   5. $c\,dL_0^2B/\epsilon^4\le N_0/3$ with the prefactor $c=2^{-19}a_Ta_\sigma/12$ of (157);
--   6. the expected-cost lower bound of Theorem 2.1 with this prefactor: every algorithm that succeeds with probability at least $2/3$ on every instance of (2) has expected query cost at least $c\,dL_0^2B/\epsilon^4$ on some instance of (2).
--
--   Differences from the source:
--   - encoding: they yield the expected-cost lower bound of Theorem 2.1 with prefactor (157) → the conclusion of theorem_2_1 with c = cPref and c₀ = c0, for every algorithm family ZOAlg d n Ω with measurable rule and every probability space of seeds; reason: same claim as the goal, with the page's explicit constants
--   - reading: satisfy the gap, smoothness and sample budgets, the list conditions and the projection bound → the explicit inequalities of pp.75–77, including T ≥ 8, T ≤ r, T ≤ m, σ² ≥ 1, the 11/48 combination of p.26 and the chain c dL₀²B/ε⁴ ≤ N₀/3 of p.77; reason: the budgets the lemma refers to
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma F.1, p.74; (150)–(157), pp.75–77

import Mathlib
import Definitions.Def_ZOGlobalLB_Params
import Definitions.Def_ZOGlobalLB_ZOAlg

open MeasureTheory
open scoped ENNReal

universe u

namespace ZOGlobalLB

/-- **Lemma F.1 (Uniform physical parameters and dimension conditions).** Xia, Yuan,
arXiv:2610.19652, Lemma F.1, p.74, with the constants (150)–(151), (157) and the verification
pp.75–77.

There is a universal `C > 0` such that, under (4) with `c₀` of (150), the choice
`T = ⌊a_T B/ϵ²⌋`, `σ² = a_σ L₀²/ϵ²`, `r = ⌊d/2⌋`, `m = d - r`, `s = m - T + 1`,
`ℓ₀ = ⌊s²σ²/(2048m)⌋`, `N₀ = ⌊a_N dTσ²⌋` and the scales `b, λ` of (126) satisfy:
* the frame dimensions: `T ≥ 8`, `T ≤ r`, `T ≤ m`, and `σ² ≥ 1` (p.75);
* the smoothness, gap and sample budgets: `λH*/b² = H`, (127) `12λT ≤ Δ` and
  `(λ/b)(c*√T + C* + √C_N σ) ≤ L₀/2` (pp.66, 75, (152));
* the one-stage list conditions (138): `s ≥ 72`, `ℓ₀ ≥ 1`, `log ℓ₀ ≤ s/8`;
* the test budget `N₀ + 1 ≤ Tℓ₀/4` (Lemmas E.3, E.4; p.76);
* the future-projection bound `p_bad = 2(N₀+1)T e^{-(r-T)/(32R²)} < 1/12` (p.76), hence for
  every `M ≥ 12N₀²` the master bound (45) is at most `11/48` (p.26);
* the numerical chain of p.77: `c dL₀²B/ϵ⁴ ≤ N₀/3` with `c = 2⁻¹⁹a_Ta_σ/12` (157);
* the expected-cost lower bound of Theorem 2.1 with the prefactor (157): every algorithm that
  succeeds with probability at least `2/3` on every instance of (2) has expected query cost at
  least `c dL₀²B/ϵ⁴` on some instance of (2).

**Formalization Note.** The last clause is the page's last sentence ("They yield the expected-cost
lower bound of Theorem 2.1, with a positive universal prefactor given in (157)"), in the form of
the goal `theorem_2_1` with the explicit `c = cPref` and `c₀ = c0`. `2⁻ᵀ` is `(1/2)^T`. -/
theorem lemma_F_1 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (L₀ Δ H ε : ℝ), 0 < L₀ → 0 < Δ → 0 < H → 0 < ε →
        ε ^ 2 ≤ c0 * Bmin Δ H L₀ →
        C * (Bmin Δ H L₀ / ε ^ 2) * Real.log (2 + Bmin Δ H L₀ * L₀ ^ 2 / ε ^ 4) ≤ (d : ℝ) →
        8 ≤ Tpar Δ H L₀ ε ∧ Tpar Δ H L₀ ε ≤ d / 2 ∧ Tpar Δ H L₀ ε ≤ d - d / 2 ∧
        1 ≤ sigmaPar L₀ ε ^ 2 ∧
        lamScale ε H * Hstar / bScale ε H ^ 2 = H ∧
        12 * lamScale ε H * Tpar Δ H L₀ ε ≤ Δ ∧
        lamScale ε H / bScale ε H *
            (cStar * Real.sqrt (Tpar Δ H L₀ ε) + CStar + Real.sqrt CN * sigmaPar L₀ ε) ≤ L₀ / 2 ∧
        72 ≤ sPar (d - d / 2) (Tpar Δ H L₀ ε) ∧
        1 ≤ ell0 (d - d / 2) (Tpar Δ H L₀ ε) (sigmaPar L₀ ε) ∧
        Real.log (ell0 (d - d / 2) (Tpar Δ H L₀ ε) (sigmaPar L₀ ε)) ≤
          (sPar (d - d / 2) (Tpar Δ H L₀ ε) : ℝ) / 8 ∧
        (N0par d (Tpar Δ H L₀ ε) (sigmaPar L₀ ε) : ℝ) + 1 ≤
          (Tpar Δ H L₀ ε : ℝ) * ell0 (d - d / 2) (Tpar Δ H L₀ ε) (sigmaPar L₀ ε) / 4 ∧
        pBad (N0par d (Tpar Δ H L₀ ε) (sigmaPar L₀ ε)) (Tpar Δ H L₀ ε) (d / 2) < 1 / 12 ∧
        (∀ M : ℕ, 12 * N0par d (Tpar Δ H L₀ ε) (sigmaPar L₀ ε) ^ 2 ≤ M →
          (1 / 2 : ℝ) ^ Tpar Δ H L₀ ε +
              pBad (N0par d (Tpar Δ H L₀ ε) (sigmaPar L₀ ε)) (Tpar Δ H L₀ ε) (d / 2) +
              (N0par d (Tpar Δ H L₀ ε) (sigmaPar L₀ ε) : ℝ) ^ 2 / M ≤ 11 / 48) ∧
        cPref * d * L₀ ^ 2 * Bmin Δ H L₀ / ε ^ 4 ≤
          (N0par d (Tpar Δ H L₀ ε) (sigmaPar L₀ ε) : ℝ) / 3 ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (A : ∀ n : ℕ, ZOAlg d n Ω),
          (∀ (n : ℕ) (F : Fin n → E d → ℝ), Admissible Δ H L₀ F →
              (2 / 3 : ℝ≥0∞) ≤ μ {ω | (A n).Succeeds ε F ω}) →
          ∃ (n : ℕ) (F : Fin n → E d → ℝ), Admissible Δ H L₀ F ∧
            ENNReal.ofReal (cPref * d * L₀ ^ 2 * Bmin Δ H L₀ / ε ^ 4) ≤
              ∫⁻ ω, ((A n).cost F ω : ℝ≥0∞) ∂μ := by sorry

end ZOGlobalLB
