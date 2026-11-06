-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_E_5
-- name    : ZOGlobalLB.lemma_E_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:47:56.431086+00:00
-- url     : https://prove2.me/theorems/f74b1d0c-3d23-44f0-bd96-92b69c0e809f
-- title:
--   Lemma E.5 — admissibility conditioning and expected cost
-- statement:
--   Let a random finite family (law $P$) and an event $E_{\mathrm{adm}}$, on which the family is admissible, satisfy $P(E_{\mathrm{adm}})\ge3/4$, and let an algorithm with independent coins satisfy $\mathbb P(\text{success},\ \text{cost}\le N_0)\le11/48$ under the joint law. If the algorithm succeeds with probability at least $2/3$ on every admissible fixed family, then on some admissible fixed family its expected query cost is at least $N_0/3$.
--
--   Differences from the source:
--   - encoding: probabilities of the events E_adm, success, cost ≤ N₀ → MeasurableSet / Measurable hypotheses for them; reason: the probabilities are taken in the paper
--   - encoding: finite-family law and algorithmic coins → product measure P ⊗ μ; reason: the coins are independent of the family
--   - encoding: a randomized adaptive algorithm → a rule jointly measurable in the seed and the history (measurable_next); reason: the run must be a random element for its probabilities and expected cost to be defined; nothing else is imposed
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma E.5, p.73, (146)–(148)

import Mathlib
import Definitions.Def_ZOGlobalLB_Admissible
import Definitions.Def_ZOGlobalLB_ZOAlg

open MeasureTheory
open scoped ENNReal

namespace ZOGlobalLB

/-- **Lemma E.5 (Admissibility conditioning and expected cost).** Xia, Yuan,
arXiv:2610.19652, Lemma E.5, p.73, (146)–(148).

Suppose an unconditioned finite-family law satisfies `P(E_adm) ≥ 3/4` and
`P(success, cost ≤ N₀) ≤ 11/48`. Every algorithm succeeding with probability at least `2/3` on
all admissible fixed families has expected query cost at least `N₀/3` on some such fixed family.

**Formalization Note.**
* The finite-family law is a random family `Fam : Ω' → (Fin n → ℝᵈ → ℝ)` on a probability space
  `(Ω', P)`; `E_adm ⊆ Ω'` is an event on which the family is admissible (class (2)). The
  algorithm `A` has seeds in `(Ω, μ)`, independent of the family: the joint law is `P ⊗ μ`.
* "Success" is eventual success (`ZOAlg.Succeeds`), "cost" is `ZOAlg.cost`.
* The paper takes the probabilities of these events, so they are events: `E_adm`, the success
  event and the cost are stated measurable (`encoding`).
* The conclusion exhibits one admissible family, which implies the worst-case form. -/
theorem lemma_E_5 {d n : ℕ} {Δ H L₀ ε : ℝ} (N₀ : ℕ)
    {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    (Fam : Ω' → Fin n → E d → ℝ) (Eadm : Set Ω') (hEadm : MeasurableSet Eadm)
    (hadm : ∀ ω' ∈ Eadm, Admissible Δ H L₀ (Fam ω')) (hP : (3 / 4 : ℝ≥0∞) ≤ P Eadm)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (A : ZOAlg d n Ω)
    (hSucc_meas : MeasurableSet {p : Ω' × Ω | A.Succeeds ε (Fam p.1) p.2})
    (hcost_meas : Measurable (fun p : Ω' × Ω => A.cost (Fam p.1) p.2))
    (hfast : (P.prod μ) {p : Ω' × Ω | A.Succeeds ε (Fam p.1) p.2 ∧
        A.cost (Fam p.1) p.2 ≤ N₀} ≤ 11 / 48)
    (hsucc : ∀ F : Fin n → E d → ℝ, Admissible Δ H L₀ F →
        (2 / 3 : ℝ≥0∞) ≤ μ {ω | A.Succeeds ε F ω}) :
    ∃ F : Fin n → E d → ℝ, Admissible Δ H L₀ F ∧
      (N₀ : ℝ≥0∞) / 3 ≤ ∫⁻ ω, (A.cost F ω : ℝ≥0∞) ∂μ := by sorry

end ZOGlobalLB
