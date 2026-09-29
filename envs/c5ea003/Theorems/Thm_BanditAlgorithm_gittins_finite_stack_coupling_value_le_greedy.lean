-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_finite_stack_coupling_value_le_greedy
-- name    : BanditAlgorithm.gittins_finite_stack_coupling_value_le_greedy
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T16:54:15.875851+00:00
-- url     : https://prove2.me/theorems/a39a5b3d-0135-4e1a-b9db-f444103760f4
-- title:
--   Greedy dominance of the finite stack-coupling value
-- statement:
--   Fix a finite horizon $N$ and use the common product space of independent arm trajectories. Let the stack-coupling value of a policy be the finite sum, over action sequences, of the policy likelihood times the discounted interleaving of the corresponding prevailing-charge stacks. If $\pi^*$ always selects an arm of maximal Gittins index, then for every Markov bandit policy $\pi$,
--
--   $$
--   V_N^{\mathrm{stack}}(\pi)\leq
--   V_N^{\mathrm{stack}}(\pi^*).
--   $$
--
--   The formula in the formal statement spells out the product trajectory measure, action likelihoods, prevailing-charge stacks, and finite discounted interleavings explicitly, so the result has no dependency on hidden proof infrastructure.
--
--   This is the stochastic common-coupling comparison in the proof of the Gittins-index theorem.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, §35.4, proof of Lemma 35.10, printed pp. 452–453 (free PDF pp. 460–461), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_GittinsPrevailingChargeValue

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_finite_stack_coupling_value_le_greedy
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    [StandardBorelSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (π πstar : MarkovBanditPolicy k S)
    (hπstar : IsGittinsIndexPolicy P r α πstar)
    (x : Fin k → S) (N : ℕ) :
    let stackValue := fun (ρ : MarkovBanditPolicy k S) ↦
      let count := fun (a : Fin N → Fin k) (i : Fin k) (t : ℕ) ↦
        ∑ s : Fin N, if (s : ℕ) < t ∧ a s = i then 1 else 0
      let historyBefore := fun (a : Fin N → Fin k)
          (ω : Fin k → ℕ → S) (t : Fin N) ↦
        ((fun u : Fin (t : ℕ) ↦
            ((fun i ↦ ω i (count a i u)),
              a ⟨u, lt_trans u.isLt t.isLt⟩)),
          fun i ↦ ω i (count a i t))
      let likelihood := fun (a : Fin N → Fin k) (ω : Fin k → ℕ → S) ↦
        ∏ t : Fin N, (ρ.select t) (historyBefore a ω t) {a t}
      let charge := fun (ω : Fin k → ℕ → S) (i : Fin k) (u : ℕ) ↦
        (Finset.range (u + 1)).inf'
          ⟨0, Finset.mem_range.2 (Nat.zero_lt_succ u)⟩
          (fun v ↦ gittinsIndex P r α (ω i v))
      let value := fun (a : Fin N → Fin k) (ω : Fin k → ℕ → S) ↦
        ∑ t : Fin N, α ^ (t : ℕ) *
          charge ω (a t) (count a (a t) t)
      let stackMeasure : Measure (Fin k → ℕ → S) :=
        Measure.pi (fun i ↦ markovChainMeasure P (x i))
      ∑ a : Fin N → Fin k,
        ∫ ω, value a ω ∂stackMeasure.withDensity (likelihood a)
    stackValue π ≤ stackValue πstar := by
  sorry
