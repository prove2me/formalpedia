-- Prove2me | solution 1 for MarkovChainCLT.partialTraj_succ_self_apply_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T20:00:09.058777+00:00
-- url     : https://prove2.me/submissions/68f907e2-d0bf-4da0-923a-15eb85168e6a

import Definitions.Def_MarkovChainPathMeasure

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology

theorem solution {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (m : ℕ) (v : Π _i : Finset.Iic m, S) :
    Kernel.partialTraj (X := fun _ : ℕ => S) (BanditAlgorithm.markovChainStep P) m (m + 1) v
      = (P (v ⟨m, Finset.mem_Iic.2 le_rfl⟩)).map
          (fun w => IicProdIoc (X := fun _ : ℕ => S) m (m + 1)
            (v, MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) m w)) := by
  have hIP : Measurable (IicProdIoc (X := fun _ : ℕ => S) m (m + 1)) := measurable_IicProdIoc
  have hPS : Measurable (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) m) :=
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) m).measurable
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _ hIP,
    Kernel.prod_apply, Kernel.id_apply, Kernel.map_apply _ hPS,
    Measure.dirac_prod, Measure.map_map hIP (by fun_prop),
    Measure.map_map (by fun_prop) hPS]
  rfl
