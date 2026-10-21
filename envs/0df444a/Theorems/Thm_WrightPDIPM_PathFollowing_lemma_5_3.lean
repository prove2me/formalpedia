-- Prove2me | Theorems.Thm_WrightPDIPM_PathFollowing_lemma_5_3
-- name    : WrightPDIPM.PathFollowing.lemma_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:53:57.387632+00:00
-- url     : https://prove2.me/theorems/babc863d-0b12-4c78-a551-42f28a45df83
-- title:
--   Lemma 5.3 — ‖UVe‖ ≤ 2^{−3/2}‖u + v‖² when uᵀv ≥ 0
-- statement:
--   Let $u, v \in \mathbb{R}^n$ with $u^{\mathsf T}v \ge 0$, and let $U = \operatorname{diag}(u_1,\dots,u_n)$, $V = \operatorname{diag}(v_1,\dots,v_n)$, so that $UVe$ is the vector of pairwise products $u_i v_i$. Then, in the Euclidean norm,
--   $$\|UVe\|_2 \le 2^{-3/2}\,\|u + v\|_2^2 .$$
--
--   This purely algebraic inequality is the engine of the bounds on the second-order term $\Delta X\Delta S e$ (Lemmas 5.4 and 5.10), applied to the scaled step components.
--
--   **Formalization Note** $2^{-3/2}$ is the real power `(2:ℝ) ^ (-(3/2))`; the norm is the explicit Euclidean norm of the setting file.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 88, Lemma 5.3

import Mathlib
import Definitions.Def_WrightPDIPM_PathFollowing_Setup

namespace WrightPDIPM.PathFollowing

/-- Lemma 5.3 (p. 88): for `u, v ∈ ℝⁿ` with `uᵀv ≥ 0`, `‖UVe‖ ≤ 2^{−3/2}‖u + v‖²`, where
`U = diag(u)`, `V = diag(v)`, so `UVe` is the vector with entries `uᵢvᵢ`; Euclidean norms. -/
theorem lemma_5_3 {n : ℕ} (u v : Fin n → ℝ) (huv : 0 ≤ u ⬝ᵥ v) :
    norm2 (fun i => u i * v i) ≤ (2 : ℝ) ^ (-((3 : ℝ) / 2)) * norm2 (u + v) ^ 2 := by sorry

end WrightPDIPM.PathFollowing
