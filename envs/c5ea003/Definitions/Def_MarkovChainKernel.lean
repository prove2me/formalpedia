-- Prove2me | Definitions.Def_MarkovChainKernel
-- name    : MarkovChainKernel
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-07-31T04:59:31.550752+00:00
-- url     : https://prove2.me/theorems/3c65b4bb-2dcf-494a-b1d7-395de1d64c5a
-- title:
--   Kernel of full Markov-chain trajectories indexed by the initial state
-- statement:
--   Given a Markov transition kernel $P$ on a measurable state space, this construction packages the law of the entire trajectory $(X_0,X_1,\ldots)$ as a Markov kernel from the initial state $x$ to trajectory space. Evaluating the kernel at $x$ is definitionally identified with the existing trajectory measure $\mathbb P_x$.
--
--   This interface makes measurability of initial-state-dependent trajectory expectations available through the standard measurable-integral API.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (Cambridge University Press, 2020), printed p. 442, Theorem 35.3 setup for a Markov reward process with initial-state laws P_x, and printed p. 448, setup preceding Assumption 35.6.

import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The Markov kernel sending an initial state to the law of the full
time-homogeneous Markov-chain trajectory started from that state. -/
noncomputable def markovChainKernel
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] : Kernel S (ℕ → S) :=
  (Kernel.traj (markovChainStep P) 0).comap
    (fun x (_ : Finset.Iic 0) ↦ x) (by fun_prop)

instance
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] :
    IsMarkovKernel (markovChainKernel P) := by
  rw [markovChainKernel]
  infer_instance

@[simp]
lemma markovChainKernel_apply
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    markovChainKernel P x = markovChainMeasure P x := by
  ext A hA
  rw [markovChainKernel, markovChainMeasure, Kernel.trajMeasure]
  rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  rw [Measure.map_dirac' (by fun_prop)]
  rw [lintegral_dirac' _
    ((Kernel.traj (markovChainStep P) 0).measurable_coe hA)]
  change
    Kernel.traj (markovChainStep P) 0 (fun _ ↦ x) A =
      Kernel.traj (markovChainStep P) 0
        ((MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ S)).symm x) A
  congr 2

end BanditAlgorithm


