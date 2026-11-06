-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_C_4
-- name    : ZOGlobalLB.lemma_C_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:50:04.111918+00:00
-- url     : https://prove2.me/theorems/e764e7f1-d0e3-494d-8865-48171d9cbe44
-- title:
--   Lemma C.4 — canonical adaptive response kernel
-- statement:
--   Fix a unit $v$ and initial data (seed) independent of all tensors. Let $\mathcal F_i$ be the initial data and the first $i$ replies. At round $i$ the label $j_i$ and point $x_i=(r_i,g_i)$ are functions of $\mathcal F_{i-1}$ and
--   $$Y_i=b_i+\langle\theta(v),\phi_i\rangle+Q_{j_i}(x_i),\qquad b_i=4(\sqrt{S(x_i)}-1),\ \phi_i=\phi(x_i).$$
--   Let $P$ project onto the span of the earlier features of label $j_i$; there are history-measurable coefficients with $P\phi_i=\sum_{t<i:\,j_t=j_i}c_{it}\phi_t$, and for any such coefficients, with $\psi_i=(I-P)\phi_i$, almost surely
--   $$Y_i\mid(v,\mathcal F_{i-1}=h)\sim\mathcal N\bigl(m_i(v,h),s_i^2(h)\bigr)\ \text{ if } s_i^2(h)>0,\qquad \delta_{m_i(h)}\ \text{ if } s_i^2(h)=0,$$
--   $$m_i(v,h)=b_i+\sum_{t<i:\,j_t=j_i}c_{it}(Y_t-b_t)+\langle\theta(v),\psi_i\rangle,\qquad s_i^2(h)=\|\psi_i\|^2 .$$
--   This holds with interleaved labels, repeated features and singular Gram matrices.
--
--   Differences from the source:
--   - encoding: the two cases of (95) → one formula gaussianReal(m_i, s_i²); reason: Mathlib's gaussianReal with variance 0 is the point mass
--   - encoding: conditional law given F_{i−1} = h, almost surely → condDistrib of Y_i given the record, a.e. in the record; reason: standard regular conditional law
--   - reading: choose history-measurable coefficients satisfying the projection identity → existence of measurable coefficients as a clause; the kernel for every measurable choice; reason: the paper constructs them (Moore–Penrose, p.50) and the kernel does not depend on the choice
--   - encoding: rounds 1, 2, … → 0-based rounds; the reply of round i is replies (i+1) (last); reason: Lean convention
--   - reading: the coefficients and variance do not depend on v; interleaved labels, repeated features, singular Gram matrices → no separate clauses; reason: they hold by construction and by the generality of the rule
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma C.4, p.49, (94)–(96)

import Mathlib
import Definitions.Def_ZOGlobalLB_OneStage

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace ZOGlobalLB

/-- **Lemma C.4 (Canonical adaptive response kernel).** Xia, Yuan, arXiv:2610.19652, Lemma C.4,
p.49, (94)–(96).

Fix a unit `v` and initial randomization and auxiliary data (the seed `X₀`) independent of all
current-stage tensors `G`. Let `F_i` contain these initial data and the first `i` queries, labels
and responses. At round `i` the label `j_i` and point `x_i = (r_i, g_i)` are `F_{i-1}`-measurable
and `Y_i = b_i + ⟨θ(v), ϕ_i⟩ + Q_{j_i}(x_i)`, `b_i = 4(√S(x_i) - 1)` (94). For the chosen label let
`P_{j_i,i-1}` project onto the span of its previous features, and choose history-measurable
coefficients with `P_{j_i,i-1}ϕ_i = Σ_{t<i : j_t = j_i} c_{it} ϕ_t`, `ψ_i = (I - P_{j_i,i-1})ϕ_i`.
Then, almost surely, `Y_i | (v, F_{i-1} = h) ∼ N(m_i(v, h), s_i²(h))` if `s_i²(h) > 0` and
`δ_{m_i(h)}` if `s_i²(h) = 0` (95), with `m_i(v, h) = b_i + Σ_t c_{it}(Y_t - b_t) + ⟨θ(v), ψ_i⟩`
and `s_i²(h) = ‖ψ_i‖²` (96). This holds with interleaved labels, repeated features and singular
Gram matrices.

**Formalization Note.**
* The tensors of all labels have law `gaussArr (J × Idx m)` (independent standard Gaussians); the
  replies use the field `Qfield` at the adaptively chosen points (the sample version of Lemma C.1).
* Rounds are 0-based: the reply of round `i` is `replies … (i + 1) (Fin.last i)`, and the record
  `F_{i-1}` is `record … i` (seed and first `i` replies); the queries are functions of the record,
  which is the measurability claim, true by construction.
* Mathlib's `gaussianReal μ 0` is the point mass `δ_μ`, so both cases of (95) are the single
  formula `gaussianReal (m_i) (s_i²)`; the conditional law is `condDistrib`, equal a.e. in the
  record. The seed space need not be standard Borel.
* The first clause gives history-measurable coefficients (as the proof does with the
  Moore–Penrose inverse, p.50); the kernel identity holds for every measurable choice. -/
theorem lemma_C_4 {m : ℕ} {σ : ℝ} (hσ : 0 < σ) {J S₀ : Type*} [MeasurableSpace J] [Countable J]
    [MeasurableSingletonClass J] [MeasurableSpace S₀] (A : OneStageRule m J S₀)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → S₀) (G : Ω → J × Idx m → ℝ) (hX₀ : Measurable X₀)
    (hG : HasLaw G (gaussArr (J × Idx m)) P) (hind : IndepFun X₀ G P)
    (v : E m) (hv : ‖v‖ = 1) (i : ℕ) :
    (∀ ω, A.replies σ v (X₀ ω) (G ω) (i + 1) (Fin.last i) =
      A.pubNow (X₀ ω) (A.replies σ v (X₀ ω) (G ω) i) +
        ⟪thetaFeat σ v, A.featNow σ (X₀ ω) (A.replies σ v (X₀ ω) (G ω) i)⟫ +
        Qfield σ (OneStageRule.labelArr (G ω) (A.query i (X₀ ω) (A.replies σ v (X₀ ω) (G ω) i)).1)
          (A.query i (X₀ ω) (A.replies σ v (X₀ ω) (G ω) i)).2.1
          (A.query i (X₀ ω) (A.replies σ v (X₀ ω) (G ω) i)).2.2) ∧
    (∃ c : S₀ × (Fin i → ℝ) → Fin i → ℝ, Measurable c ∧ ∀ h, A.IsProjCoef σ h.1 h.2 (c h)) ∧
    ∀ c : S₀ × (Fin i → ℝ) → Fin i → ℝ, Measurable c → (∀ h, A.IsProjCoef σ h.1 h.2 (c h)) →
      ∀ᵐ h ∂(P.map (fun ω => A.record σ v (X₀ ω) (G ω) i)),
        condDistrib (fun ω => A.replies σ v (X₀ ω) (G ω) (i + 1) (Fin.last i))
            (fun ω => A.record σ v (X₀ ω) (G ω) i) P h =
          gaussianReal (A.condMean σ v h.1 h.2 (c h)) (‖A.resid σ h.1 h.2‖ ^ 2).toNNReal := by sorry

end ZOGlobalLB
