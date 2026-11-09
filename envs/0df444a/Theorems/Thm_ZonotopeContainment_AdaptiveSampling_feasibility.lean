-- Prove2me | Theorems.Thm_ZonotopeContainment_AdaptiveSampling_feasibility
-- name    : ZonotopeContainment.AdaptiveSampling.feasibility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:17:45.142875+00:00
-- url     : https://prove2.me/theorems/6b6e3ca0-3823-4efa-bbb6-991c7064d64f
-- title:
--   §2.2 (p. 7) — feasibility and spanning invariants
-- statement:
--   Let $d\ge3$, $C\ge64$, $w_1,\ldots,w_n\in\mathbb R^d$, and let $T$ be an approximate Lewis map for $w$. For every realization of a run, let $(v_j,A_j)$ denote the state before iteration $j$, including the final state $j=R$. Then initially $A_0v_{0,i}=w_i$, and at every $0\le j\le R$ the generators span $\mathbb R^d$ and
--   $$A_jv_{j,i}=\theta_{j,i}w_i\quad\text{for some }0<\theta_{j,i}\le1,\qquad A_j Z(v_j)\subseteq Z(w).$$
--   At every executed iteration $j<R$, the computed matrix $S_j$ is positive definite, the local sample $x_j$ lies in $Z(v_j)$, each update satisfies $A_{j+1}v_{j+1,i}=q_{j,i}A_jv_{j,i}$ with the iteration's weights $q_{j,i}$, and the recorded point satisfies
--   $$x_{\mathrm{orig},j}\in Z(w).$$
--   This deterministic statement makes every rejected membership query a valid witness in $Z(w)\setminus Q$; no exceptional Gaussian realizations are excluded.
--
--   Differences from the source:
--   - encoding: Euclidean vectors, finite generator lists and matrix formulas → EuclideanSpace ℝ (Fin d), Fin n generator families and real matrices acting by toEuclideanLin; reason: these preserve the Euclidean inner product, the ℓ₂ norm and all finite sums
--   - encoding: generator terms divided by their Euclidean norm → zero generators have zero projection and matrix contribution, weight one, and stay zero; reason: deleting or adding zero generators changes neither the zonotope nor any nonzero-generator update
--   - generalization: the computational input model uses rational generator matrices → arbitrary real generator families; reason: the geometric and Gaussian statements apply to these families and specialize to rational input
--   - generalization: a fixed absolute algorithm constant C ≥ 64 → every C ≥ 64, with existential constants chosen after C where needed; reason: the analysis fixes C first and chooses the remaining constants afterwards, uniformly in all other data
--   - generalization: T is computed once in a preprocessing step, by approximating Lewis weights (p. 5) → any invertible matrix T with ¼I ⪯ L(Tw) ⪯ I, taken as an input (ApproxLewis w T); its computation is not formalized; reason: Algorithm 1 uses T only through these properties, so the statement covers every map the preprocessing can return
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), §2.2, p. 7, paragraph after the display defining S, x and v⁺; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Algorithm

open scoped MatrixOrder

namespace ZonotopeContainment.AdaptiveSampling

/-- §2.2, p. 7: deterministic invariants and feasibility for every draw sequence. -/
theorem feasibility (d n : ℕ) (hd : 3 ≤ d) (C : ℝ) (hC : 64 ≤ C)
    (w : Fin n → E d) (T : Mat d) (hT : ApproxLewis w T) (z : Tape d) :
    (∀ i, act (runState C w T z 0).A ((runState C w T z 0).v i) = w i) ∧
    (∀ j ≤ rounds d,
      Submodule.span ℝ (Set.range (runState C w T z j).v) = ⊤ ∧
      (∀ i, ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
        act (runState C w T z j).A ((runState C w T z j).v i) = θ • w i) ∧
      (act (runState C w T z j).A) '' zonotope (runState C w T z j).v ⊆ zonotope w) ∧
    (∀ j : Fin (rounds d),
      (weightedMatrix (runState C w T z j).v
        (weights C (scale d j) (runState C w T z j).v (z j))).PosDef ∧
      localPoint C (scale d j) (runState C w T z j).v (z j) ∈
        zonotope (runState C w T z j).v ∧
      (∀ i, act (runState C w T z (j + 1)).A ((runState C w T z (j + 1)).v i) =
        weights C (scale d j) (runState C w T z j).v (z j) i •
          act (runState C w T z j).A ((runState C w T z j).v i)) ∧
      recorded C w T z j ∈ zonotope w) := by sorry

end ZonotopeContainment.AdaptiveSampling
