-- Prove2me | Theorems.Thm_KServer_martingale_abs_anticoncentration
-- name    : KServer.martingale_abs_anticoncentration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-01T09:34:37.955811+00:00
-- url     : https://prove2.me/theorems/5bfbcb58-b4c1-4e53-ad3d-8b31fbc93d3a
-- title:
--   Elementary anti-concentration for stopped bounded-increment martingales
-- statement:
--   **Anti-concentration for finite discrete martingales**: if the increments are bounded, $|X_j| \le \gamma$, and the total conditional variance lies in the window $[T_0, B]$ on every path, then
--
--   $$T_0^{\,3} \;\le\; \bigl(\mathbb{E}\,|S_N|\bigr)^2 \cdot \bigl(8B^2 + 3\gamma^2 B\bigr),$$
--
--   i.e. $\mathbb{E}|S_N| = \Omega\bigl(T_0^{3/2}/B\bigr)$ — of order $\sqrt{T}$ when the window is $[T - O(1), T]$.
--
--   ## Role
--
--   This replaces Ibragimov's quantitative martingale central limit theorem in the Bubeck–Coester–Rabani lower bound (STOC 2023, Lemma 9): their stage-2a imbalance martingale is stopped when its accumulated conditional variance reaches $\approx \alpha\beta w^2/4$, and the recurrence $C_{w+1} \ge C_w + \Omega(\sqrt{C_w})$ needs exactly $\mathbb{E}|S_\kappa| = \Omega(\sqrt{\alpha\beta}\,w)$ — which this bound provides with a worse constant, absorbed into the choice of $\alpha$. Stopping is handled by zeroing increments beyond the stopping time, which stays inside the `IsDiscreteMartingale` interface.
--
--   ## Proof idea
--
--   Three elementary steps. (i) Orthogonality: $\mathbb{E}[S^2] = \mathbb{E}[\sum v_j] \in [T_0, B]$. (ii) A fourth-moment bound $\mathbb{E}[S^4] \le 8B\,\mathbb{E}[S^2] + 3\gamma^2 B$: expanding $\mathbb{E}[S_{k+1}^4]$, the odd term vanishes, the cross terms are dominated using $|\mathbb{E}[X^3\,|\,\cdot]| \le \gamma v$ and $4\gamma|S|v \le 2S^2v + 2\gamma^2 v$, and the accumulated $\mathbb{E}[v_k S_k^2]$ grows to $\mathbb{E}[v_k S_N^2] \le B\,\mathbb{E}[S_N^2]$ by conditional second-moment monotonicity. (iii) Cauchy–Schwarz twice, in polynomial form: $(\mathbb{E} S^2)^2 \le \mathbb{E}|S| \cdot \mathbb{E}|S|^3$ and $(\mathbb{E}|S|^3)^2 \le \mathbb{E} S^2 \cdot \mathbb{E} S^4$, so $(\mathbb{E} S^2)^3 \le (\mathbb{E}|S|)^2\, \mathbb{E} S^4$.
-- source:
--   Elementary replacement for I. A. Ibragimov's martingale CLT convergence rate as used in S. Bubeck, C. Coester, Y. Rabani, STOC 2023, Lemma 9; via a fourth-moment supermartingale bound and Cauchy–Schwarz.

import Mathlib
import Definitions.Def_KServer_discrete_martingale

namespace KServer

theorem martingale_abs_anticoncentration {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (P : Ω → ℝ) (N : ℕ) (hist : ℕ → Ω → ℕ) (X v : ℕ → Ω → ℝ)
    (H : IsDiscreteMartingale P N hist X v) (γ B T₀ : ℝ) (hγ : 0 ≤ γ)
    (hX : ∀ j, j < N → ∀ ω, |X j ω| ≤ γ)
    (hv0 : ∀ j, j < N → ∀ ω, 0 ≤ v j ω)
    (hVB : ∀ ω, ∑ j ∈ Finset.range N, v j ω ≤ B)
    (hVT : ∀ ω, T₀ ≤ ∑ j ∈ Finset.range N, v j ω)
    (hT₀ : 0 ≤ T₀) (hB : 0 ≤ B) (hPsum : ∑ ω, P ω = 1) :
    T₀ ^ 3 ≤ (∑ ω, P ω * |mgSum X N ω|) ^ 2 * (8 * B ^ 2 + 3 * γ ^ 2 * B) := by sorry

end KServer
