-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_current_terminal_potential_le_stack_envelope
-- name    : BanditAlgorithm.gittins_current_terminal_potential_le_stack_envelope
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T17:05:32.600011+00:00
-- url     : https://prove2.me/theorems/0c5cdae3-1248-4058-a79b-390c2ba32d66
-- title:
--   Pathwise Gittins terminal-potential envelope
-- statement:
--   On a common stack realization of the arms, consider any length-$N$ interleaving. The sum of the arms' current Gittins retirement values after this history is bounded above by an explicit nonnegative envelope. For each arm, the envelope consists of the absolute discounted-reward values at its first $N+1$ stack states, together with a geometric factor multiplying its initial absolute value and the absolute rewards observed along the first $N$ subsequent stack states.
--
--   $$
--   U_N(\omega,a)\le E_N(\omega).
--   $$
--
--   This pathwise bound is uniform over the action interleaving and supplies the domination needed to remove the terminal retirement term in the finite-horizon Gittins comparison.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, §35.4, proof of Lemma 35.10, printed pp. 452–453 (free PDF pp. 460–461), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_GittinsTerminalPotential

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_current_terminal_potential_le_stack_envelope
    {k N : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (ω : Fin k → ℕ → S) (a : Fin N → Fin k) :
    let count := fun (i : Fin k) (t : ℕ) ↦
      ∑ s : Fin N, if (s : ℕ) < t ∧ a s = i then 1 else 0
    let stackHistory : MarkovBanditHistory k S N :=
      ((fun t ↦ ((fun i ↦ ω i (count i t)), a t)),
        fun i ↦ ω i (count i N))
    let absoluteValue := fun y : S ↦
      ∫ path, ∑' t : ℕ, α ^ t * |r (path t)|
        ∂markovChainMeasure P y
    let envelope := ∑ i : Fin k,
      ((∑ u ∈ Finset.range (N + 1), absoluteValue (ω i u)) +
        (∑' t : ℕ, α ^ t) *
          (absoluteValue (ω i 0) +
            ∑ v ∈ Finset.range N, |r (ω i (v + 1))|))
    currentGittinsRetirementPotential P r α stackHistory ≤ envelope := by
  sorry
