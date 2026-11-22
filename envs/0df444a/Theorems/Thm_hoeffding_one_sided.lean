-- Prove2me | Theorems.Thm_hoeffding_one_sided
-- name    : hoeffding_one_sided
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:34:34.363396+00:00
-- url     : https://prove2.me/theorems/6c56771a-cb3f-48b9-adbf-c36aabd05a91
-- title:
--   hoeffding one sided: hoeffding one sided
-- statement:
--   One-sided Hoeffding: for iid Bernoulli(p) draws, the empirical average
--       undershoots the mean by ≥ t with probability ≤ exp(-2mt²).
--
--       **Proof strategy (3 steps):**
--
--       1. **MGF bound (Hoeffding's lemma):** For X ∈ [0,1] with E[X] = p,
--          E[exp(s(X-p))] ≤ exp(s²/8).
--          - Adapt from `cosh_le_exp_sq_half` infrastructure in Rademacher.lean.
--          - Key: convexity of exp on [0,1] gives E[exp(sX)] ≤ p·exp(s) + (1-p)·exp(0),
--            then the s²/8 bound follows from ln(1 + x) ≤ x and Taylor expansion.
--          ```
--          have mgf_bound : ∀ (s : ℝ),
--            ∫ x, Real.exp (s * (indicator x - p)) ∂D ≤ Real.exp (s^2 / 8) := by ...
--          ```
--
--       2. **Product independence:** E[exp(s·∑(X_i-p))] = ∏ E[exp(s(X_i-p))] ≤ exp(ms²/8).
--          - Uses `MeasureTheory.Measure.pi` independence structure.
--          - Needs: `Measure.pi` integral factorization for product of functions.
--          - MEASURABILITY: `fun xs => Real.exp (s * ∑ i, f (xs i))` is measurable
--            (composition of measurable functions).
--          ```
--          have product_bound : ∀ (s : ℝ),
--            ∫ xs, Real.exp (s * ∑ i, (indicator (xs i) - p)) ∂Measure.pi (fun _ => D)
--            ≤ Real.exp (m * s^2 / 8) := by ...
--          ```
--
--       3. **Exponential Markov + optimize:** P[∑(X_i-p) ≤ -mt]
--          = P[exp(-s·∑(X_i-p)) ≥ exp(smt)] ≤ exp(-smt + ms²/8).
--          Optimize over s: set s = 4t to get ≤ exp(-2mt²).
--          - Uses Markov's inequality in ENNReal form.
--          - CAST ISSUE: Markov gives ENNReal bound, need to convert exp(-2mt²) between
--            ENNReal.ofReal and the measure value.
--          ```
--          have markov_step : ∀ (s : ℝ) (hs : 0 < s),
--            Measure.pi (fun _ => D) {xs | ∑ i, (indicator (xs i) - p) ≤ -(m : ℝ) * t}
--            ≤ ENNReal.ofReal (Real.exp (-(s * m * t) + m * s^2 / 8)) := by ...
--          have optimize : Real.exp (-(4*t * m * t) + m * (4*t)^2 / 8)
--            = Real.exp (-2 * m * t^2) := by ring_nf
--          ```
--
--       **CAST ISSUES to watch:**
--       - `m : ℕ` needs cast to `ℝ` in the exponent: `(m : ℝ)`
--       - `EmpiricalError` returns `ℝ`, `TrueErrorReal` returns `ℝ`, good — no ENNReal gap
--       - The measure value is `ENNReal`, the bound `exp(-2mt²)` is `ℝ≥0∞` via `ENNReal.ofReal`
--
--       **References:** SSBD Lemma B.3, Hoeffding (1963)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L162-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Complexity/Symmetrization.lean#L162-L219

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Mathlib.Probability.Moments.SubGaussian
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Symmetrization
set_option autoImplicit true
@[expose] public section
public section
universe u v
open MeasureTheory ENNReal

theorem hoeffding_one_sided {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m)
    (t : ℝ) (ht : 0 < t) (_ht1 : t ≤ 1)
    (hmeas : MeasurableSet {x | h x ≠ c x}) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      {xs : Fin m → X | EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
        (zeroOneLoss Bool) ≤ TrueErrorReal X h c D - t}
    ≤ ENNReal.ofReal (Real.exp (-2 * ↑m * t ^ 2)) := by sorry
