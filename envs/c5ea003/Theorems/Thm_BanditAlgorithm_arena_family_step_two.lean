-- Prove2me | Theorems.Thm_BanditAlgorithm_arena_family_step_two
-- name    : BanditAlgorithm.arena_family_step_two
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-04T23:06:15.340338+00:00
-- url     : https://prove2.me/theorems/4acf3a01-cc87-4387-bc75-0c71ad5f551c
-- title:
--   Step 2 of the MDP lower bound: some family member forces regret $\gtrsim \sqrt{Dkn}$
-- statement:
--   **Step 2 of the $\Omega(\sqrt{DSAn})$ MDP lower bound: the change-of-measure core.**
--
--   Fix a layered arena $E_0$ and a family $(E_p)_{p}$ of arenas that agree with $E_0$ off a single transition row, member $E_p$ planting an advantage $\Delta$ at the leaf--action pair $p$. Let $k$ be the number of members and fix an arbitrary learner $\pi$. If the advantage is tuned to
--   $$\Delta \;=\; \frac{c_1(k-1)}{2}\sqrt{\frac{D}{2c_2 n k}},$$
--   then **some** member of the family forces $\pi$ into expected regret at least
--   $$\frac{c_1^2 c_3}{16}\sqrt{\frac{Dkn}{2c_2}} \;-\; \frac{1/2+\Delta}{\delta},$$
--   the subtracted term being the cost of a single transient episode.
--
--   The argument is the classical one. No learner can distinguish $k$ alternatives that differ in one row without paying for it: the counts it allocates to the $k$ planted pairs sum to a fixed budget, so by pigeonhole some pair receives at most a $1/k$ share, and the divergence decomposition then bounds the KL divergence between that alternative and the reference by $\mathbb{E}_0[N] \cdot d(\tfrac12, \tfrac12+\Delta)$, which the tuning of $\Delta$ keeps below a constant.
--
--   The hypotheses are exactly the arithmetic facts the parameter tuning must check. `hlo`, `htail1` and `htail2` deliver the lower bound of Claim 38.10 through a Chernoff certificate for the truncated leaf counter; `hhi` gives its upper bound; `hcapD` says the truncation level $N$ lies below the pathwise cap $n/D$; and `hc3D` calibrates $c_3$ against $\delta^{-1}$, which plays the role of the diameter in Claim 38.11.
--
--   The counting is done with truncated counts rather than a stopping time: `truncCount` records the visits to a pair among the first $N$ rounds spent at leaves. This yields $\sum_p T_p = \min(\text{total}, N)$ and $T_p \le N_n(p)$ *pathwise*, which is what licenses the bounded change-of-measure inequality without any measurability side conditions.
-- source:
--   ORIGIN: Thomas Jaksch, Ronald Ortner, Peter Auer, 'Near-optimal Regret Bounds for Reinforcement Learning', JMLR 11 (2010) 1563-1600, Theorem 5 (p. 1567) and its proof in Section 6 'The Lower Bound', pp. 1582-1586. JAO prove: for S, A >= 10, D >= 20 log_A S and T >= DSA there is an MDP with S states, A actions and diameter D forcing expected regret >= 0.015 sqrt(DSAT). EXPOSITION FOLLOWED HERE: Lattimore-Szepesvari, Bandit Algorithms, Cambridge 2020, Theorem 38.7 (p. 529) and Section 38.7 (pp. 529-534), which restates the result for S >= 3, A >= 2, D >= 6 + 2 log_A S. DEVIATION: L&S build 'a tree of minimum depth' (p. 529); this node instead places every leaf at the SAME depth. With leaves at two depths an episode through a shallow leaf is one round shorter, worth about delta/2 of gain, while the planted advantage is only Delta = Theta(sqrt(kD/n)), so for large n the optimal gain is attained at a leaf carrying no advantage and L&S Claim 38.11 fails. JAO avoid this because their tree only connects the s-circle states and is collapsed in the analysis. This node supplies the change-of-measure step (JAO eqs. (34)-(37) and Lemma 13, pp. 1583-1585; L&S Claims 38.9-38.11).

import Definitions.Def_LayeredArena
import Mathlib.Data.Real.Sqrt

open MeasureTheory ProbabilityTheory
open scoped NNReal
open BanditAlgorithm BanditAlgorithm.LayeredArena

theorem BanditAlgorithm.arena_family_step_two
    {S A : ℕ} [NeZero S] {δ Δ : ℝ≥0}
    (hδ1 : δ ≤ 1) (hδ0 : (0 : ℝ) < δ) (hΔ4 : Δ ≤ 1 / 4) (hΔ2 : Δ ≤ 1 / 2)
    (E₀ : LayeredArena S A)
    (Efam : ↥(countedPairs E₀.leafNat) → LayeredArena S A)
    (hg : ∀ p, E₀.good = (Efam p).good) (hb : ∀ p, E₀.bad = (Efam p).bad)
    (hr : ∀ p, E₀.root = (Efam p).root) (hl : ∀ p, E₀.lvl = (Efam p).lvl)
    (hdp : ∀ p, E₀.depth = (Efam p).depth) (hc : ∀ p, E₀.child = (Efam p).child)
    (hsl : ∀ p, (Efam p).specialLeaf = p.val.1)
    (hsa : ∀ p, (Efam p).specialAction = p.val.2)
    (hS : 0 < S) (hA : 0 < A)
    (π : MDPPolicy S A) (n N k : ℕ) (D c₁ c₂ c₃ : ℝ)
    (hcard : Fintype.card ↥(countedPairs (A := A) E₀.leafNat) = k) (hk : 2 ≤ k)
    (hn0 : 0 < n) (hN0 : 0 < N) (hD : 0 < D)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hcapD : (N : ℝ) ≤ n / D) (hc₃D : c₃ * D ≤ 1 / (δ : ℝ))
    (ε : ℝ) (hlo : c₁ * n / D ≤ (1 - ε) * N)
    (hhi : ((n : ℝ) + 1 / (δ : ℝ)) / E₀.epiLen (δ : ℝ) ≤ c₂ * n / D)
    (htail1 : E₀.depth + N * (E₀.depth + 2) ≤ n)
    (htail2 : (2 : ℝ) ^ N ≤ ε * (1 + (δ : ℝ)) ^ N
      * (mx (δ : ℝ)) ^ (n - E₀.depth - N * (E₀.depth + 2)))
    (hΔtune : (Δ : ℝ) = c₁ * ((k : ℝ) - 1) / 2 * Real.sqrt (D / (2 * c₂ * n * k))) :
    ∃ p : ↥(countedPairs E₀.leafNat),
      c₁ ^ 2 * c₃ / 16 * Real.sqrt (D * k * n / (2 * c₂)) - (1 / 2 + (Δ : ℝ)) / (δ : ℝ)
        ≤ ∫ h, mdpRegret ((Efam p).toMDP hδ1 hΔ2) n h
            ∂(mdpMeasure ((Efam p).toMDP hδ1 hΔ2)
              (mdpStateDirac (Efam p).root) π n) := by
  sorry
