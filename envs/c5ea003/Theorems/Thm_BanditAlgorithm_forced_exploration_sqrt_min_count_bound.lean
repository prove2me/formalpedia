-- Prove2me | Theorems.Thm_BanditAlgorithm_forced_exploration_sqrt_min_count_bound
-- name    : BanditAlgorithm.forced_exploration_sqrt_min_count_bound
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T23:19:00.309792+00:00
-- url     : https://prove2.me/theorems/ec6d2a94-ee40-4add-ac56-ff325cd94456
-- title:
--   Forced exploration keeps every count above $\sqrt t-2k$
-- statement:
--   Let $N_i(t)$ be counts on $k\ge1$ arms that start at zero and increase by exactly one coordinate per round, the coordinate played at round $t$ being $\mathrm{arm}(t)$, and let $m(t)=\min_i N_i(t)$. Suppose the rule is *forced to explore*: whenever $m(t)<\lfloor\sqrt t\rfloor$ it must play a least-played arm, $N_{\mathrm{arm}(t)}(t)=m(t)$. Then for every $t$,
--   $$t\ <\ (m(t)+1)^2+k\,m(t)+k,$$
--   so $m(t)>\sqrt t-k-1$: every arm is played at least of order $\sqrt t$ times, whatever the rule does on the unforced rounds.
--
--   The proof is a potential argument, and the potential is what makes the constants explicit. Let $c(t)$ be the number of coordinates attaining the minimum and set $\Phi(t)=k\,m(t)+k-c(t)$. Then $\Phi$ never decreases, and it strictly increases on every forced round: if two or more coordinates are minimal, incrementing one leaves $m$ alone and drops $c$ by one; if only one is minimal, incrementing it raises $m$ by one, adding $k$ to the first term while the second loses at most $k-1$. Since $\Phi(0)=0$ and $\Phi(t)\le k\,m(t)+k-1$, at most $k\,m(t)+k-1$ of the first $t$ rounds can have been forced. Hence every window of $k\,m(t)+k$ consecutive rounds before $t$ contains an unforced round, at which the threshold was already below the minimum; monotonicity of $\lfloor\sqrt{\cdot}\rfloor$ and of $m$ then transports that bound to the start of the window.
--
--   Stated for an abstract count sequence, with the minimum supplied as a function $m$ together with the two properties that characterise it, so that no lattice-valued definition is needed.
-- source:
--   Garivier & Kaufmann, Optimal Best Arm Identification with Fixed Confidence, COLT 2016 (arXiv:1602.04589), Lemma 7 (the forced-exploration half of D-Tracking); the potential-function proof and the explicit constants are as stated here.

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Nat

theorem BanditAlgorithm.forced_exploration_sqrt_min_count_bound {k : ℕ} (hk : 0 < k)
    (N : ℕ → Fin k → ℕ) (arm : ℕ → Fin k) (m : ℕ → ℕ)
    (hmle : ∀ t i, m t ≤ N t i) (hmatt : ∀ t, ∃ i, N t i = m t)
    (hinit : ∀ i, N 0 i = 0)
    (hstep : ∀ t i, N (t + 1) i = N t i + (if i = arm t then 1 else 0))
    (hforced : ∀ t, m t < Nat.sqrt t → N t (arm t) = m t) (t : ℕ) :
    t < (m t + 1) * (m t + 1) + k * m t + k := by
  sorry
