-- Prove2me | Theorems.Thm_mme_CW_coupled_floor_pruning
-- name    : mme_CW_coupled_floor_pruning
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-07T14:47:38.510004+00:00
-- url     : https://prove2.me/theorems/1cfcbccf-1312-484f-b08f-2ae1621795a7
-- title:
--   Admissibility of the coupled floor profile at every q
-- statement:
--   Fix $q\ge 3$ and $\tau$ with $3\tau\ge 2$, and set
--   $$\lambda \;=\; \frac{2}{q^{3\tau}+2},\qquad L=\lfloor \lambda N\rfloor,\qquad G=N-L .$$
--   Then for all sufficiently large $N$ one has $L>0$, $G>0$, $L+G=N$ and $341L<100G$.
--
--   Here $\lambda$ is the fraction of the $N$ tensor positions that Coppersmith--Winograd assign to the two "low" blocks $\langle 1,q,1\rangle$ of the coupled constituent, the remaining $G$ positions carrying the two coupled $\langle q,1,q\rangle$ blocks. The last conjunct is the margin the hashing step consumes: since $G/L\to q^{3\tau}/2$ and $q\ge3$, $3\tau\ge2$ give $q^{3\tau}\ge 9$, the limiting ratio is at least $4.5$, comfortably above $3.41$. The quantitative input is `mme_CW_coupled_pruning_ratio`, which supplies $341/100 < q^{3\tau}/2$ for exactly this range of $q$ and $\tau$.
--
--   This is the general-$q$ form of `mme_CW_q6_coupled_exact_floor_pruning`, additionally recording $0<G$, which the capacity estimate needs and which does not follow from $L>0$ and $L+G=N$ alone (truncated subtraction allows $G=0$ when $L=N$).
-- source:
--   Don Coppersmith and Shmuel Winograd, Matrix multiplication via arithmetic progressions, Journal of Symbolic Computation 9(3), 1990, 251-280; the coupled four-sum constituent (d) on printed p. 266 and its value lemma on printed p. 270. General-q form of the q=6 chain used for omega < 2.376.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Filter

theorem mme_CW_coupled_floor_pruning
    (q : ℕ) (hq : 3 ≤ q) (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((q : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      0 < L ∧ 0 < G ∧ L + G = N ∧ 341 * L < 100 * G := by
  sorry
