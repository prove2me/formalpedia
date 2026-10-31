-- Prove2me | Theorems.Thm_KServer_race_kernel_moments
-- name    : KServer.race_kernel_moments
-- status  : Proved
-- author  : @kwal0203
-- created : 2026-10-30T16:52:59.964127+00:00
-- url     : https://prove2.me/theorems/e5338bb8-1310-44c5-9b3f-3e78aa95a715
-- title:
--   Exact second and fourth moment identities for a balanced race
-- statement:
--   Let $\Omega$ be a finite set, let $P_\omega$ be real weights, and let $S_j,L_j,R_j$ be real-valued arrays for $0\le j\le n$. Suppose $S_0=0$, every denominator $L_j+R_j$ is nonzero for $j<n$, and for every real test function $f$ the averaged transition identity holds:
--
--   $$\sum_\omega P_\omega f(S_{j+1})=\sum_\omega P_\omega\left[\frac{R_j}{L_j+R_j}f(S_j+L_j)+\frac{L_j}{L_j+R_j}f(S_j-R_j)\right].$$
--
--   Then the terminal second and fourth moments satisfy the exact identities
--
--   $$\sum_\omega P_\omega S_n^2=\sum_{j<n}\sum_\omega P_\omega L_jR_j,$$
--
--   $$\sum_\omega P_\omega S_n^4=\sum_{j<n}\sum_\omega P_\omega L_jR_j\left(6S_j^2+4S_j(L_j-R_j)+L_j^2-L_jR_j+R_j^2\right).$$
--
--   Every term inside a weighted sum is evaluated at the same outcome $\omega$. These formulas turn terminal-moment conditions into sums of local race quantities. When the weights are probabilities and the two step sizes are nonnegative, the transition is the balanced left/right race used by BCR. The fourth-moment formula retains the asymmetric cubic contribution.
--
--   **Formalization Note** The theorem is algebraic: it does not need positivity or normalization of the weights, or positivity of the step sizes. It includes $n=0$. The averaged transition identity is the exact hypothesis; no stronger filtration-adaptedness claim is implicit.
-- source:
--   S. Bubeck, C. Coester, Y. Rabani, The Randomized k-Server Conjecture Is False!, https://arxiv.org/html/2211.05753v2, Section 4.1, stage 2a (transition probabilities), and Section 4.2, equations (3) and (4), printed pp. 16–19. Second identity: elementary fourth-power expansion of the same transition kernel, proved here; the paper states the conditional second moment in equation (4).

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

theorem KServer.race_kernel_moments {Ω : Type*} [Fintype Ω] (P : Ω → ℝ)
    (S L R : ℕ → Ω → ℝ) (n : ℕ) (hzero : ∀ ω, S 0 ω = 0)
    (hden : ∀ j < n, ∀ ω, L j ω + R j ω ≠ 0)
    (hstep : ∀ j < n, ∀ f : ℝ → ℝ,
      (∑ ω, P ω * f (S (j + 1) ω)) =
        ∑ ω, P ω * (R j ω / (L j ω + R j ω) * f (S j ω + L j ω) +
          L j ω / (L j ω + R j ω) * f (S j ω - R j ω))) :
    (∑ ω, P ω * S n ω ^ 2) = ∑ j ∈ Finset.range n, ∑ ω, P ω * (L j ω * R j ω) ∧
    (∑ ω, P ω * S n ω ^ 4) = ∑ j ∈ Finset.range n, ∑ ω,
      P ω * (L j ω * R j ω * (6 * S j ω ^ 2 + 4 * S j ω * (L j ω - R j ω) +
        L j ω ^ 2 - L j ω * R j ω + R j ω ^ 2)) := by sorry
