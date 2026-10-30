-- Prove2me | Theorems.Thm_XinMartingaleInventory_Minimax_lemma_10
-- name    : XinMartingaleInventory.Minimax.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T23:59:11.548473+00:00
-- url     : https://prove2.me/theorems/6cea0b0a-c0e4-4b5d-8900-436d83ce599b
-- title:
--   Lemma 10 — Two-point affine-majorant certificate
-- statement:
--   Let U>0 and μ be rational; f is bounded on the real interval [0,U]. The following is the literal printed endpoint reading.
--
--   Lemma 10. Suppose f : [0,U] → ℝ is any bounded real-valued function with domain [0,U]. Suppose 0 ≤ L ≤ μ < R ≤ U, and the linear function η(d) ≜ ((f(R)−f(L))/(R−L))d + (Rf(L)−Lf(R))/(R−L), i.e. the line intersecting f at the points L and R, satisfies η(d) ≥ f(d) for all d ∈ [0,U], i.e. lies above f on [0,U]. Then the measure q s.t. q(L) = (R−μ)/(R−L), q(R) = (μ−L)/(R−L), belongs to arg max_{Q∈M(μ)} E_Q[f(D)].
--
--   Differences from the source:
--   - encoding: probability laws on rational vectors and their expectations → nonnegative real atom masses with HasSum equal to one, and countable weighted sums; reason: rational finite histories are countable and bounded observables are summable; no finite-support restriction
--   - reading: Lemma 10 displays endpoints L and R in the real interval without specifying rationality → L and R range over real numbers; M(μ) remains rationally supported; reason: retain the literal displayed endpoint scope and record the rational-support conflict in INSIGHTS.yaml
--   - encoding: the proposed real-endpoint measure belongs to an argmax of rationally supported laws → there exists a rational atom law with the same real atom masses that attains the maximum; reason: equality of these atomic probability measures is exactly equality of all real atom masses
--   - encoding: a function defined on the stated interval → a total real function whose values and hypotheses are used only on that interval; reason: every function on the interval has such an extension and all conclusions depend only on its restriction
-- source:
--   Xin and Goldberg, arXiv:1511.09437v2, Lemma 10, p.22 (PDF p.22)

import Definitions.Def_XinMartingaleInventory_Minimax_constructions
import Definitions.Def_XinMartingaleInventory_Minimax_continuation

namespace XinMartingaleInventory.Minimax

theorem lemma_10 (U μ : ℚ) (hU : 0 < U) (f : ℝ → ℝ)
    (hbounded : ∃ K : ℝ, ∀ d ∈ Set.Icc (0 : ℝ) (U : ℝ), |f d| ≤ K)
    (L R : ℝ) (hL : 0 ≤ L) (hLμ : L ≤ (μ : ℝ)) (hμR : (μ : ℝ) < R)
    (hRU : R ≤ (U : ℝ))
    (hmajor : ∀ d ∈ Set.Icc (0 : ℝ) (U : ℝ), f d ≤ chord f L R d) :
    ∃ q : DemandLaw, q ∈ meanLaws U μ ∧ realAtoms q = realTwoPoint L R μ ∧
      ∀ q' ∈ meanLaws U μ,
        expectation q' (fun d => f (d : ℝ)) ≤ expectation q (fun d => f (d : ℝ)) := by sorry

end XinMartingaleInventory.Minimax
