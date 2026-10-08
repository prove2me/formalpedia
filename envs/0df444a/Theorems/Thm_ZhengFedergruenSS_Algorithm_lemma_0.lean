-- Prove2me | Theorems.Thm_ZhengFedergruenSS_Algorithm_lemma_0
-- name    : ZhengFedergruenSS.Algorithm.lemma_0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:56:29.444714+00:00
-- url     : https://prove2.me/theorems/28a3e33a-5fd1-4fbd-adac-c604a9fdf0a0
-- title:
--   Lemma 0, p. 656 — how c(s − 1, S) compares with c(s, S) and G(s)
-- statement:
--   In the model of Zheng and Federgruen, fix $S$ and $s<S$.
--
--   1. If $G(s)<c(s,S)$ then $G(s)<c(s-1,S)\le c(s,S)$.
--   2. If $G(s)=c(s,S)$ then $G(s)=c(s-1,S)=c(s,S)$.
--   3. If $G(s)>c(s,S)$ then $G(s)>c(s-1,S)\ge c(s,S)$.
--   4. If $G(s)<c(s-1,S)$ then $c(s-1,S)\le c(s,S)$.
--   5. If $G(s)=c(s-1,S)$ then $c(s-1,S)=c(s,S)$.
--   6. If $G(s)>c(s-1,S)$ then $c(s-1,S)\ge c(s,S)$.
--
--   Items 1–3 are part (a) of the lemma and items 4–6 part (b). These comparisons drive both loops of the algorithm.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, p. 656, Lemma 0

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand
import Definitions.Def_ZhengFedergruenSS_Algorithm_Model

namespace ZhengFedergruenSS.Algorithm

/-- Lemma 0, p. 656 (Zheng and Federgruen 1991). For any fixed `S` and `s < S`:
(a) `G(s) < (=, >) c(s − 1, S) ⩽ (=, ⩾) c(s, S)` if `G(s) < (=, >) c(s, S)`;
(b) `c(s − 1, S) ⩽ (=, ⩾) c(s, S)` if `G(s) < (=, >) c(s − 1, S)`.
All six readings are stated; in (a) the first comparison is strict and the second weak, as printed. -/
theorem lemma_0 (D : VeinottWagnerSS.RenewalCost.DemandDist) (hp0 : D.φ 0 < 1)
    (K : ℝ) (hK : 0 < K) (G : ℤ → ℝ) (hG : NegUnimodal G) (hgrowth : GrowthCond K G)
    (s S : ℤ) (hsS : s < S) :
    (G s < c D.φ K G s S → G s < c D.φ K G (s - 1) S ∧ c D.φ K G (s - 1) S ≤ c D.φ K G s S) ∧
    (G s = c D.φ K G s S → G s = c D.φ K G (s - 1) S ∧ c D.φ K G (s - 1) S = c D.φ K G s S) ∧
    (G s > c D.φ K G s S → G s > c D.φ K G (s - 1) S ∧ c D.φ K G (s - 1) S ≥ c D.φ K G s S) ∧
    (G s < c D.φ K G (s - 1) S → c D.φ K G (s - 1) S ≤ c D.φ K G s S) ∧
    (G s = c D.φ K G (s - 1) S → c D.φ K G (s - 1) S = c D.φ K G s S) ∧
    (G s > c D.φ K G (s - 1) S → c D.φ K G (s - 1) S ≥ c D.φ K G s S) := by sorry

end ZhengFedergruenSS.Algorithm
