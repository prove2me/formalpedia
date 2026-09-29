-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_finite_prevailing_charge_eq_stack_coupling_value
-- name    : BanditAlgorithm.gittins_finite_prevailing_charge_eq_stack_coupling_value
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T16:53:53.744517+00:00
-- url     : https://prove2.me/theorems/6cb46ead-55fa-4e4f-ae84-1505252a90e6
-- title:
--   Finite prevailing-charge stack-coupling representation
-- statement:
--   Fix a finite horizon $N$, an initial state vector, and a Markov bandit policy $\pi$. On a common product space, sample one independent infinite Markov trajectory for each arm. For every length-$N$ action sequence, weight the associated interleaving of the arms' prevailing-charge stacks by the likelihood that $\pi$ follows that action sequence. Then the resulting finite sum of weighted stack integrals is exactly the policy's expected finite discounted prevailing-charge value:
--
--   $$
--   C_N^\pi
--   =\sum_{a}\int\sum_{t=0}^{N-1}\alpha^t
--   v_{a_t}\!\left(T_{a_t}(t)\right)L_\pi(a,\omega)\,dM_x(\omega).
--   $$
--
--   Here $M_x$ is the product law of the independent arm trajectories, $L_\pi(a,\omega)$ is the action-sequence likelihood, and $T_i(t)$ counts prior selections of arm $i$.
--
--   This theorem isolates the finite common-stack coupling identity used in the Gittins-index comparison.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, §35.4, proof of Lemma 35.10, printed pp. 452–453 (free PDF pp. 460–461), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_GittinsPrevailingChargeValue

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_finite_prevailing_charge_eq_stack_coupling_value
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π : MarkovBanditPolicy k S) (x : Fin k → S) (N : ℕ) :
    let count := fun (a : Fin N → Fin k) (i : Fin k) (t : ℕ) ↦
      ∑ s : Fin N, if (s : ℕ) < t ∧ a s = i then 1 else 0
    let historyBefore := fun (a : Fin N → Fin k)
        (ω : Fin k → ℕ → S) (t : Fin N) ↦
      ((fun u : Fin (t : ℕ) ↦
          ((fun i ↦ ω i (count a i u)),
            a ⟨u, lt_trans u.isLt t.isLt⟩)),
        fun i ↦ ω i (count a i t))
    let likelihood := fun (a : Fin N → Fin k) (ω : Fin k → ℕ → S) ↦
      ∏ t : Fin N, (π.select t) (historyBefore a ω t) {a t}
    let charge := fun (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) ↦
      (Finset.range (u + 1)).inf'
        ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ u)⟩
        (fun v ↦ gittinsIndex P r α (ω i v))
    let value := fun (a : Fin N → Fin k) (ω : Fin k → ℕ → S) ↦
      ∑ t : Fin N, α ^ (t : ℕ) *
        charge ω (a t) (count a (a t) t)
    let stackMeasure : Measure (Fin k → ℕ → S) :=
      Measure.pi (fun i ↦ markovChainMeasure P (x i))
    markovBanditFinitePrevailingChargeValue P r α π x N =
      ∑ a : Fin N → Fin k,
        ∫ ω, value a ω ∂stackMeasure.withDensity (likelihood a) := by
  sorry
