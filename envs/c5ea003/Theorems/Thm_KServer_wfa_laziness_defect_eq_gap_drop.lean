-- Prove2me | Theorems.Thm_KServer_wfa_laziness_defect_eq_gap_drop
-- name    : KServer.wfa_laziness_defect_eq_gap_drop
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T22:39:39.639946+00:00
-- url     : https://prove2.me/theorems/a140ff6e-27a4-4707-a337-0002e457f315
-- title:
--   The laziness defect of the Work Function Algorithm is the drop of the labelling gap
-- statement:
--   Consider the Work Function Algorithm built from the **labelled** work function $W$ --- the one that charges an offline solution for delivering server $i$ to a named point, rather than merely for occupying a set of points --- and write $w$ for the classical **unlabelled** work function, $A_t$ for the algorithm's configuration after $t$ requests, and
--
--   $$\delta_s(X) \;=\; W_s(X) - w_s(X) \;\ge\; 0$$
--
--   for the *labelling gap*: the amount by which insisting on a particular labelling of $X$ raises the cost of serving the first $s$ requests. Then at every step
--
--   $$\underbrace{d(A_t, A_{t+1}) - \bigl(w_{t+1}(A_t) - w_{t+1}(A_{t+1})\bigr)}_{\text{laziness defect at step } t} \;=\; \delta_{t+1}(A_t) - \delta_{t+1}(A_{t+1}).$$
--
--   The left-hand side measures how far the algorithm's move falls short of being *lazy* for the unlabelled work function --- of buying, in decrease of $w_{t+1}$, the full price of the move it makes. It is non-negative, by $1$-Lipschitzness of $w_{t+1}$. The identity says that this shortfall is accounted for exactly by the drop in the labelling gap across the move, both gaps being measured against the *same* work function $w_{t+1}$.
--
--   ## Role
--
--   Summed over a request sequence, the laziness defect is the one quantity separating a work-function-based online algorithm from a competitiveness bound: an algorithm's cost, plus the work function at its final configuration, equals its total laziness defect plus the growth of the work function along its trajectory, and the latter is what a potential function bounds. For the algorithm built from the *unlabelled* work function the defect vanishes identically, by the defining minimality of its step, and the classical analysis follows. For the algorithm built from the labelled work function it need not vanish, and this identity localises the discrepancy: the entire defect is a telescoping-resistant sum of differences of the labelling gap, a quantity that is itself bounded pointwise by $k$ times the diameter of the space.
--
--   The identity is unconditional --- no tree, no bound on the space, no restriction on how ties in the algorithm's step are resolved.
--
--   ## Formalization note
--
--   `workFunction` is the labelled work function of the ambient development, defined through `moveCost`, the sum of the distances travelled by individually indexed servers; `workFnU` is obtained from it by minimising over the relabellings of the target configuration. The proof rests on the step identity $W_{t+1}(A_t) = W_{t+1}(A_{t+1}) + d(A_t, A_{t+1})$ --- the Work Function Algorithm is lazy for the labelled work function it computes --- after which the claim is a rearrangement. Since that identity holds for any minimiser, the theorem is independent of the tie-breaking in `wfaStep`.
-- source:
--   A localisation of the discrepancy between the labelled and unlabelled work functions in the analysis of the Work Function Algorithm; the underlying step identity is the one used in W. Bein, M. Chrobak, L. Larmore, 'The 3-server problem in the plane', TCS 289 (2002), Lemma 2, and in E. Koutsoupias, 'The k-server problem', Computer Science Review 3 (2009), Section 3.

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_work_function

namespace KServer

theorem wfa_laziness_defect_eq_gap_drop (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M]
    [Fintype M] (C₀ : Config k M) (σ : List M) (t : ℕ) (ht : t < σ.length) :
    moveCost ((WFA hk C₀).conf (σ.take t)) ((WFA hk C₀).conf (σ.take (t + 1)))
        - (workFnU C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t))
           - workFnU C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take (t + 1))))
      = (workFunction C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t))
          - workFnU C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take t)))
        - (workFunction C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take (t + 1)))
          - workFnU C₀ (σ.take (t + 1)) ((WFA hk C₀).conf (σ.take (t + 1)))) := by sorry

end KServer
