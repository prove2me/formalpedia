-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_E_3
-- name    : ZOGlobalLB.lemma_E_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:51:30.925702+00:00
-- url     : https://prove2.me/theorems/e7973754-27e1-4a84-a6bd-1b10add68b9d
-- title:
--   Lemma E.3 — conditional stage charging
-- statement:
--   Let $s=m-T+1$ and $\ell_0=\lfloor s^2\sigma^2/(2048m)\rfloor$ satisfy (138): $s\ge72$, $\ell_0\ge1$, $\log\ell_0\le s/8$. In the ideal experiment with any simulated algorithm:
--
--   1. each stage $k$ has conditional probability at most $1/16$, given $\mathcal G_{<k}$, of being born and completing within $\ell_0$ of its tests;
--   2. if $N+1\le T\ell_0/4$, the probability that all $T$ stages complete within $N+1$ tests is at most $2^{-T}$.
--
--   No independence of stage durations is assumed.
--
--   Differences from the source:
--   - generalization: conditional probability given the stage's starting history → conditional on G_{<k} (133); reason: G_{<k} contains the birth history (Lemma E.2); the paper's proof conditions on it first
--   - encoding: tests → paid queries and the final output, counted by simState; padding (0,0) after the output; reason: as on p.71
--   - reading: ℓ₀ chosen below (138) → (138) as hypotheses with s = m − T + 1; reason: the conditions the lemma uses
--   - encoding: the algorithm in the simulated experiment → SimAlg, which also sees gate bits and disclosed frames; reason: only strengthens the algorithm (p.68)
--   - encoding: conditional probability of the fast-stage event → the event is also stated measurable; reason: a conditional probability presupposes an event; condExp of a non-measurable indicator is 0
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma E.3, p.69, (138)–(142)

import Mathlib
import Definitions.Def_ZOGlobalLB_IsHaarFrame
import Definitions.Def_ZOGlobalLB_Simulator
import Definitions.Def_ZOGlobalLB_Params

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZOGlobalLB

/-- **Lemma E.3 (Conditional stage charging).** Xia, Yuan, arXiv:2610.19652, Lemma E.3, p.69,
(138)–(142).

With the per-stage budget `ℓ₀ = ⌊s²σ²/(2048m)⌋`, `s = m - T + 1`, under (138) (`s ≥ 72`,
`ℓ₀ ≥ 1`, `log ℓ₀ ≤ s/8`), each stage has conditional probability at most `1/16` of completing
within `ℓ₀` tests. If `N + 1 ≤ Tℓ₀/4`, the probability that all stages complete within `N + 1`
tests is at most `2⁻ᵀ`. No independence of stage durations is assumed.

**Formalization Note.**
* The experiment is the ideal independent-label experiment of Lemma E.2: seed `X₀`, Haar frames
  `U`, `V`, Gaussian tensors `G` of a countable label set, mutually independent; `B` is an
  arbitrary simulated algorithm (it also sees gate bits and disclosed frames, which only
  strengthens it). A test is a paid query or the final output (`simState` counts both).
* The per-stage bound is stated conditionally on the enlarged pre-birth σ-algebra `G_{<k}` (133),
  which contains the birth history (Lemma E.2); conditioning on the birth history follows by the
  tower property (`generalization`). "Completing within `ℓ₀` tests" is `StageFast` (born, and the
  stage counter passes `k` within `ℓ₀` tests of the birth); an unborn stage is not fast.
* The fast-stage events are also stated measurable, so that their conditional probabilities are
  genuine (`condExp` of a non-measurable indicator would be `0`).
* "No independence of stage durations is assumed" is a remark: no such hypothesis appears.
* `2⁻ᵀ` is `(1/2)^T`. -/
theorem lemma_E_3 {r m T : ℕ} (hT : 1 ≤ T) {σ : ℝ} (hσ : 0 < σ) (hs : 72 ≤ sPar m T)
    (hℓ₀ : 1 ≤ ell0 m T σ) (hlog : Real.log (ell0 m T σ) ≤ (sPar m T : ℝ) / 8)
    {J S₀ : Type*} [MeasurableSpace J] [Countable J] [MeasurableSingletonClass J]
    [MeasurableSpace S₀] {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → S₀) (U : Ω → Fin T → E r) (V : Ω → Fin T → E m)
    (G : Ω → J × (Fin T × Idx m) → ℝ)
    (hX₀ : Measurable X₀) (hU : IsHaarFrame P U) (hV : IsHaarFrame P V) (hGm : Measurable G)
    (hG : HasLaw G (gaussArr (J × (Fin T × Idx m))) P)
    (hind : IndepFun X₀ (fun ω => (U ω, V ω, G ω)) P ∧ IndepFun U (fun ω => (V ω, G ω)) P ∧
      IndepFun V G P)
    (B : SimAlg r m J S₀) :
    (∀ k : Fin T,
      MeasurableSet {ω | StageFast B σ (U ω) (V ω) (G ω) (X₀ ω) (ell0 m T σ) k} ∧
      P[({ω | StageFast B σ (U ω) (V ω) (G ω) (X₀ ω) (ell0 m T σ) k}).indicator (fun _ => (1 : ℝ))
          | Gless X₀ U V G k] ≤ᵐ[P] fun _ => (1 / 16 : ℝ)) ∧
    ∀ N : ℕ, (N : ℝ) + 1 ≤ (T : ℝ) * ell0 m T σ / 4 →
      P {ω | T ≤ (simState B σ (U ω) (V ω) (G ω) (X₀ ω) (N + 1)).1} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ T) := by sorry

end ZOGlobalLB
