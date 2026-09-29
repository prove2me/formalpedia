-- Prove2me | solution 1 for Erdos180.proposedFamily_isCyclic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:39:36.175299+00:00
-- url     : https://prove2.me/submissions/b0363bc5-2a50-4f46-a0d7-a49b290dd3d1

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Theorems.Thm_Erdos180_encodeFiniteGraph_not_acyclic
import Theorems.Thm_Erdos180_not_acyclic_of_eight_cycle_copy
import Theorems.Thm_Erdos180_proposedFamily_induction

namespace Erdos180

noncomputable section
open Finset SimpleGraph

lemma jTheta_quotient_injective
    {f : JVertex → JVertex} (hf : JAdmissible f)
    (copy : Fin 2) :
    Function.Injective (fun v : SubdivisionVertex 2 =>
      f (jThetaVertex copy v)) := by
  intro u v heq
  have htemplate : jThetaVertex copy u = jThetaVertex copy v :=
    hf.2.2 copy (jThetaVertex_mem copy u)
      (jThetaVertex_mem copy v) heq
  exact (jThetaCopy copy).injective htemplate

theorem jQuotient_not_acyclic
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    ¬ (encodeFiniteGraph (quotientGraph jTemplate f)).graph.IsAcyclic := by
  apply encodeFiniteGraph_not_acyclic
  apply not_acyclic_of_eight_cycle_copy
  exact (copyToQuotient thetaGraph jTemplate f (jThetaCopy 0)
    (jTheta_quotient_injective hf 0)).comp thetaCycleCopy

lemma kGamma_quotient_injective
    {f : KVertex → KVertex} (hf : KAdmissible f)
    (copy : Fin 2) :
    Function.Injective (fun v : SubdivisionVertex 3 =>
      f (kGammaVertex copy v)) := by
  intro u v heq
  have htemplate : kGammaVertex copy u = kGammaVertex copy v :=
    hf.2 copy (show (kGammaVertex copy u).1 = copy from rfl)
      (show (kGammaVertex copy v).1 = copy from rfl) heq
  exact (kGammaCopy copy).injective htemplate

theorem kQuotient_not_acyclic
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    ¬ (encodeFiniteGraph (quotientGraph kTemplate f)).graph.IsAcyclic := by
  apply encodeFiniteGraph_not_acyclic
  apply not_acyclic_of_eight_cycle_copy
  exact (copyToQuotient gammaGraph kTemplate f (kGammaCopy 0)
    (kGamma_quotient_injective hf 0)).comp gammaCycleCopy

theorem four_cycle_not_acyclic :
    ¬ (finiteCycle 4).graph.IsAcyclic := by
  intro h
  exact h (SimpleGraph.cycleGraph.cycle 1)
    SimpleGraph.cycleGraph.isCycle_cycle

theorem six_cycle_not_acyclic :
    ¬ (finiteCycle 6).graph.IsAcyclic := by
  intro h
  exact h (SimpleGraph.cycleGraph.cycle 3)
    SimpleGraph.cycleGraph.isCycle_cycle

end

end Erdos180

open Erdos180
open Finset SimpleGraph

theorem solution : IsCyclicFamily proposedFamily :=
  proposedFamily_induction (P := fun graph => ¬ graph.graph.IsAcyclic)
    four_cycle_not_acyclic six_cycle_not_acyclic
    (fun _ hf => jQuotient_not_acyclic hf)
    (fun _ hf => kQuotient_not_acyclic hf)
