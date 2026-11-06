-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_C_5
-- name    : ZOGlobalLB.lemma_C_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:49:51.99318+00:00
-- url     : https://prove2.me/theorems/9db023ed-42f6-44b5-a2ac-3680f26d5422
-- title:
--   Lemma C.5 — posterior regularity and information under arbitrary reuse
-- statement:
--   Let $v$ be uniform on the unit sphere of a known $s$-dimensional subspace of $\mathbb R^m$, $s\ge4$, and let the seed (coins and auxiliary data), $v$ and the tensors be independent. For any adaptive rule making $n$ queries, with label reuse and interleaving:
--
--   1. the record $\mathcal F_n$ has a common reference measure $\nu$: there is a jointly measurable likelihood $L(u,t)>0$ with $P_{v}=L(v,\cdot)\,\nu$ for every unit $v$ in the subspace;
--   2. for almost every record $t$, the posterior density $p_t(v)=L(v,t)/z_t$, $z_t=\int L(u,t)\pi(du)\in(0,\infty)$, is positive and $C^1$ on the sphere, and it is the posterior (Bayes' formula for the joint law of $(v,\mathcal F_n)$);
--   3. $$I(v;\mathcal F_n)\le\frac{10mn}{(s-2)\sigma^2}.$$
--
--   The seed and record spaces need not be standard Borel.
--
--   Differences from the source:
--   - encoding: a known s-dimensional subspace → the image of an isometric embedding ι : ℝˢ → ℝᵐ, v = ιV with V uniform on the sphere of ℝˢ; reason: same object
--   - encoding: common reference measure → ∃ ν and a jointly measurable positive L with P_{ιu} = L(u,·)ν; reason: the content of (107)
--   - reading: posterior density → p_t = L/z_t with 0 < z_t < ∞ a.e., C¹ via u ↦ p_t(u/‖u‖) on ℝˢ ∖ {0}, and Bayes' formula; reason: the paper's construction p.54
--   - encoding: I(v; F_n) → mutualInfo (KL of the joint law from the product of marginals) in [0,∞]; reason: the bound also states finiteness
--   - encoding: labels → a countable label type with the discrete σ-algebra; reason: as on p.18
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma C.5, p.52, (107)–(109)

import Mathlib
import Definitions.Def_ZOGlobalLB_OneStage
import Definitions.Def_OnlineConvexOpt_BanditConvex_UniformOnUnitSphere_v2
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZOGlobalLB

/-- **Lemma C.5 (Posterior regularity and information under arbitrary reuse).** Xia, Yuan,
arXiv:2610.19652, Lemma C.5, p.52, (107)–(109).

Let `v` have the uniform prior `π` on the unit sphere of a known `s`-dimensional subspace of
`ℝᵐ`, `s ≥ 4`. Initial auxiliary data and algorithmic coins are independent of `v` and the fields.
For any `n` adaptive scalar queries, including label reuse and interleaving, the complete record
has a common reference measure. Its posterior density is positive and `C¹` on the sphere for
almost every record, and `I(v; F_n) ≤ 10mn/((s - 2)σ²)`. The seed and record spaces need not be
standard Borel.

**Formalization Note.**
* The subspace is the image of an isometric embedding `ι : ℝˢ → ℝᵐ`, and `v = ι V` with `V`
  uniform on the unit sphere of `ℝˢ` (`IsUniformOnUnitSphere`, platform definition). The seed
  `X₀` (coins and auxiliary data), `V` and the tensors `G` are mutually independent; `G` has law
  `gaussArr`.
* Common reference measure (107): a measure `ν` on records and a jointly measurable likelihood
  `L(u, t) > 0` with `P_{ιu} = L(u, ·) ν` for every unit `u`, where `P_{ιu}` is the law of the
  record when the parameter is `ιu`.
* The posterior density with respect to the prior is `p_t(u) = L(u, t)/z_t`,
  `z_t = ∫ L(u, t) π(du)`; for almost every record, `0 < z_t < ∞`, `p_t` is `C¹` on the sphere
  (`u ↦ p_t(u/‖u‖)` is `C¹` on `ℝˢ ∖ {0}`), and `p_t` is the posterior: Bayes' formula for the joint
  law of `(V, F_n)`.
* `I(v; F_n)` is the platform's `mutualInfo` (KL divergence of the joint law from the product of
  the marginals, in `ℝ≥0∞`), so the bound also states finiteness. -/
theorem lemma_C_5 {m s n : ℕ} (hs : 4 ≤ s) {σ : ℝ} (hσ : 0 < σ) {J S₀ : Type*}
    [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J] [MeasurableSpace S₀]
    (ι : E s →ₗᵢ[ℝ] E m) (A : OneStageRule m J S₀)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : Ω → E s) (X₀ : Ω → S₀) (G : Ω → J × Idx m → ℝ)
    (hV : OnlineConvexOpt.BanditConvex.IsUniformOnUnitSphere P V) (hX₀ : Measurable X₀)
    (hG : HasLaw G (gaussArr (J × Idx m)) P)
    (hind : IndepFun (fun ω => (X₀ ω, V ω)) G P ∧ IndepFun X₀ V P) :
    (∃ (ν : Measure (S₀ × (Fin n → ℝ))) (L : E s → S₀ × (Fin n → ℝ) → ℝ),
      Measurable (Function.uncurry L) ∧
      (∀ u ∈ Metric.sphere (0 : E s) 1, ∀ t, 0 < L u t) ∧
      (∀ u ∈ Metric.sphere (0 : E s) 1,
        P.map (fun ω => A.record σ (ι u) (X₀ ω) (G ω) n) =
          ν.withDensity (fun t => ENNReal.ofReal (L u t))) ∧
      (∀ᵐ t ∂(P.map (fun ω => A.record σ (ι (V ω)) (X₀ ω) (G ω) n)),
        0 < ∫⁻ u, ENNReal.ofReal (L u t) ∂(P.map V) ∧
        ∫⁻ u, ENNReal.ofReal (L u t) ∂(P.map V) < ⊤ ∧
        ContDiffOn ℝ 1 (fun u : E s => L (‖u‖⁻¹ • u) t /
          (∫⁻ u', ENNReal.ofReal (L u' t) ∂(P.map V)).toReal) {u | u ≠ 0}) ∧
      ∀ B : Set (E s × (S₀ × (Fin n → ℝ))), MeasurableSet B →
        P.map (fun ω => (V ω, A.record σ (ι (V ω)) (X₀ ω) (G ω) n)) B =
          ∫⁻ t, ∫⁻ u, B.indicator 1 (u, t) * (ENNReal.ofReal (L u t) /
              ∫⁻ u', ENNReal.ofReal (L u' t) ∂(P.map V)) ∂(P.map V)
            ∂(P.map (fun ω => A.record σ (ι (V ω)) (X₀ ω) (G ω) n))) ∧
    ThompsonTutorial.InfoRatio.mutualInfo P (fun ω => ι (V ω))
        (fun ω => A.record σ (ι (V ω)) (X₀ ω) (G ω) n) ≤
      ENNReal.ofReal (10 * m * n / (((s : ℝ) - 2) * σ ^ 2)) := by sorry

end ZOGlobalLB
