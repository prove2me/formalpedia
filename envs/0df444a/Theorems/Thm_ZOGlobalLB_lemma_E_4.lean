-- Prove2me | Theorems.Thm_ZOGlobalLB_lemma_E_4
-- name    : ZOGlobalLB.lemma_E_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:51:37.823146+00:00
-- url     : https://prove2.me/theorems/bb5e14f0-a193-4315-83c7-4b1889ac06a1
-- title:
--   Lemma E.4 — static-oracle coupling and finite-pool error
-- statement:
--   Let $U,V$ be independent Haar frames, the tensors of $M\ge1$ base labels independent standard Gaussians, $\pi$ a uniformly random permutation of the $2M$ public labels, and the algorithm's seed, all mutually independent. Assume (138) and $N\le M$, $N+1\le T\ell_0/4$. For every algorithm run on the static finite population (128) — with adaptive labels, reuse and an arbitrary final output —
--   $$\mathbb P\bigl(\text{stationary success with at most } N \text{ queries}\bigr)\le2^{-T}+2(N+1)T\,e^{-(r-T)/(32R^2)}+\frac{N^2}{M},\qquad R=64\sqrt T .$$
--
--   Differences from the source:
--   - reading: the static oracle and the simulator admit a coupling under which success has probability at most … → the bound on the static experiment; reason: the static success probability does not depend on the coupling, which is the proof device
--   - reading: ℓ₀ of Lemma E.3 → (138) as hypotheses; reason: needed for the 2^{-T} term
--   - encoding: independence of U, V, tensors, permutation and coins → a chain of IndepFun; reason: mutual independence
--   - encoding: M base labels → M ≥ 1; reason: the population is nonempty
--   - encoding: a randomized adaptive algorithm → a rule jointly measurable in the seed and the history (measurable_next); reason: the run must be a random element for its probabilities and expected cost to be defined; nothing else is imposed
-- source:
--   Xia, Yuan, On Global Joint Lower Bounds in Zeroth-Order Nonconvex Optimization, arXiv:2610.19652, Lemma E.4, p.72, (143)–(145)

import Mathlib
import Definitions.Def_ZOGlobalLB_ZOAlg
import Definitions.Def_ZOGlobalLB_IsHaarFrame
import Definitions.Def_ZOGlobalLB_Population

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ZOGlobalLB

/-- **Lemma E.4 (Static-oracle coupling and finite-pool error).** Xia, Yuan, arXiv:2610.19652,
Lemma E.4, p.72, (143)–(145).

For `N ≤ M` and `N + 1 ≤ Tℓ₀/4` (with `ℓ₀` and the conditions (138) of Lemma E.3), the static
finite oracle and the prefix simulator admit a coupling under which stationary success by `N`
queries has probability at most `2⁻ᵀ + 2(N + 1)T e^{-(r-T)/(32R²)} + N²/M`. Labels may be chosen
adaptively and reused, and the final output may be arbitrary.

The experiment: independent Haar frames `U` (in `ℝʳ`) and `V` (in `ℝᵐ`), independent standard
Gaussian tensors for `M` base labels, a uniformly random permutation `π` of the `2M` public labels
hiding the antithetic pairing, and the algorithm's seed, all mutually independent. The algorithm
`A` is an arbitrary `ZOAlg` on `ℝ^{r+m}` with `2M` labels, run on the static population (128).

**Formalization Note.**
* The statement is the bound (145) on the static experiment; the coupling with the prefix
  simulator is the proof device (`reading`): the static success probability does not depend on
  how it is coupled.
* "Stationary success by `N` queries" is `ZOAlg.Succeeds` (the output `x̂` has
  `‖∇f(x̂)‖ ≤ ϵ` for the population mean `f = λF_new(·/b)`) with `cost ≤ N`.
* Mutual independence of the five random elements is written as a chain of `IndepFun`.
* `2⁻ᵀ` is `(1/2)^T`; `R = 64√T`; `M ≥ 1` (the population has `2M ≥ 2` labels). -/
theorem lemma_E_4 {r m T M N : ℕ} {ε H σ : ℝ} (hε : 0 < ε) (hH : 0 < H) (hσ : 0 < σ)
    (hT : 1 ≤ T) (hM : 1 ≤ M)
    (hs : 72 ≤ sPar m T) (hℓ₀ : 1 ≤ ell0 m T σ)
    (hlog : Real.log (ell0 m T σ) ≤ (sPar m T : ℝ) / 8)
    (hNM : N ≤ M) (hN : (N : ℝ) + 1 ≤ (T : ℝ) * ell0 m T σ / 4)
    {Ω S₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace S₀] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (U : Ω → Fin T → E r) (V : Ω → Fin T → E m) (G : Ω → Fin M × (Fin T × Idx m) → ℝ)
    (π : Ω → Equiv.Perm (Fin (M + M))) (seed : Ω → S₀)
    (hU : IsHaarFrame P U) (hV : IsHaarFrame P V)
    (hG : HasLaw G (gaussArr (Fin M × (Fin T × Idx m))) P)
    (hπ : HasLaw π (PMF.uniformOfFintype (Equiv.Perm (Fin (M + M)))).toMeasure P)
    (hseed : Measurable seed)
    (hind : IndepFun U (fun ω => (V ω, G ω, π ω, seed ω)) P ∧
      IndepFun V (fun ω => (G ω, π ω, seed ω)) P ∧
      IndepFun G (fun ω => (π ω, seed ω)) P ∧ IndepFun π seed P)
    (A : ZOAlg (r + m) (M + M) S₀) :
    P {ω | A.Succeeds ε (population ε H σ (U ω) (V ω) (π ω) (G ω)) (seed ω) ∧
        A.cost (population ε H σ (U ω) (V ω) (π ω) (G ω)) (seed ω) ≤ N} ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ T + pBad N T r + (N : ℝ) ^ 2 / M) := by sorry

end ZOGlobalLB
