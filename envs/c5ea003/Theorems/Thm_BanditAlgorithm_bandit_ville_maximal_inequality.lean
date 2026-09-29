-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_ville_maximal_inequality
-- name    : BanditAlgorithm.bandit_ville_maximal_inequality
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T21:30:54.481531+00:00
-- url     : https://prove2.me/theorems/061f75f8-383c-4f2c-93d6-53a31fff6f1a
-- title:
--   Ville's maximal inequality for a bandit exponential weight
-- statement:
--   **Ville's maximal inequality** in the canonical bandit model. Let $W_n$ be a nonnegative process on length-$n$ histories with unit mass, $\mathbb E[W_0]=1$, satisfying the martingale property in its integrated form
--   $$\int F(\text{prefix}_n\,\omega)\,W_{n+1}(\text{prefix}_{n+1}\,\omega)\,dP=\int F(\text{prefix}_n\,\omega)\,W_n(\text{prefix}_n\,\omega)\,dP$$
--   for every measurable $F\ge0$ on length-$n$ histories. Then for every level $c$,
--   $$c\cdot P\bigl(\exists n,\ W_n\ge c\bigr)\le 1.$$
--
--   The point is the *absence of any union over rounds*: a fixed-round Chernoff bound controls $P(W_n\ge c)$ for each $n$ separately, and unioning costs a factor growing with the horizon, whereas the maximal inequality is uniform in $n$ at no cost. This is what makes the time-uniform threshold $\beta_t(\delta)=k\log(t^2+t)+f^{-1}(\delta)$ of Lattimore--Szepesv\'ari Lemma 33.7 achievable at all — a union over rounds would force a threshold linear in $t$.
--
--   The martingale hypothesis is stated in integrated form rather than as $\mathbb E[W_{n+1}\mid\mathcal F_n]=W_n$ because that is exactly what the one-step exponential tilt identity of the canonical model supplies; the two are equivalent here, and no conditional expectations are needed anywhere. The proof is optional stopping arranged so that only the one-step identity is used: writing $A_N$ for "no crossing up to $N$", the induction hypothesis $\int_{A_N}W_N\,dP+c\,P(E_N)\le1$ is advanced by splitting $A_N$ at the level $c$ of $W_{N+1}$ and recombining, which is legitimate precisely because $A_N$ is a function of the length-$N$ history.
-- source:
--   Ville, Etude critique de la notion de collectif (Gauthier-Villars, 1939): the maximal inequality for nonnegative martingales. Stated here for the canonical bandit model. It is the device that makes a time-uniform threshold possible at all, and is used in this development to prove the pairwise deviation bound behind L&S Lemma 33.7.

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory Real NNReal ENNReal

theorem BanditAlgorithm.bandit_ville_maximal_inequality {k : ℕ}
    (P : MeasureTheory.Measure (ℕ → Fin k × ℝ))
    (W : (n : ℕ) → BanditAlgorithm.BanditHistory k n → ENNReal)
    (hmeas : ∀ n, Measurable (W n))
    (hinit : ∫⁻ ω, W 0 (BanditAlgorithm.banditTrajPrefix k 0 ω) ∂P = 1)
    (hstep : ∀ (n : ℕ) (F : BanditAlgorithm.BanditHistory k n → ENNReal), Measurable F →
      ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
          * W (n + 1) (BanditAlgorithm.banditTrajPrefix k (n + 1) ω) ∂P
        = ∫⁻ ω, F (BanditAlgorithm.banditTrajPrefix k n ω)
          * W n (BanditAlgorithm.banditTrajPrefix k n ω) ∂P)
    (c : ENNReal) :
    c * P {ω : ℕ → Fin k × ℝ |
        ∃ i : ℕ, c ≤ W i (BanditAlgorithm.banditTrajPrefix k i ω)} ≤ 1 := by
  sorry
