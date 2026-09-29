-- Prove2me | solution 1 for BanditAlgorithm.mdp_measure_map_restrict
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-02T04:49:18.403026+00:00
-- url     : https://prove2.me/submissions/1e2bf834-b061-45f0-8372-71b74a9c85dc

import Definitions.Def_FiniteMDPLearning
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory BanditAlgorithm

/-!
The trajectory measures of an MDP form a projective family: the law of the
first `m` rounds of an `n`-round trajectory is the law of an `m`-round
trajectory.  The one-round case is the statement that the marginal of a
composition-product on its first factor is the first factor.
-/

variable {S A : ℕ}

/-- Restricting a trajectory of `n` rounds to its first `m` rounds. -/
private def restrictTraj {m n : ℕ} (hmn : m ≤ n) (h : MDPTrajectory S A n) :
    MDPTrajectory S A m :=
  fun t ↦ h (Fin.castLE hmn t)

private lemma measurable_restrictTraj {m n : ℕ} (hmn : m ≤ n) :
    Measurable (restrictTraj (S := S) (A := A) hmn) := by
  rw [measurable_pi_iff]
  exact fun t ↦ measurable_pi_apply _

/-- Forgetting the last round of a trajectory of `n + 1` rounds. -/
private lemma map_init (M : FiniteMDP S A) (μ0 : MDPStateDistribution S)
    (π : MDPPolicy S A) (n : ℕ) :
    (mdpMeasure M μ0 π (n + 1)).map (fun h ↦ Fin.init h) = mdpMeasure M μ0 π n := by
  have hinit : Measurable (fun h : MDPTrajectory S A (n + 1) ↦ Fin.init h) := by
    rw [measurable_pi_iff]
    exact fun t ↦ measurable_pi_apply _
  rw [mdpMeasure, Measure.map_map hinit measurable_mdpTrajectorySnoc]
  have hcomp : (fun h : MDPTrajectory S A n × (Fin S × Fin A) ↦
      Fin.init (Fin.snoc (α := fun _ ↦ Fin S × Fin A) h.1 h.2)) = Prod.fst := by
    funext h
    exact Fin.init_snoc (α := fun _ ↦ Fin S × Fin A) h.2 h.1
  rw [Function.comp_def, hcomp]
  exact Measure.fst_compProd _ _

/-- **The trajectory measures are projective** (L&S §38.1, Figure 38.1). -/
theorem solution (M : FiniteMDP S A)
    (μ0 : MDPStateDistribution S) (π : MDPPolicy S A) {m n : ℕ} (hmn : m ≤ n) :
    (mdpMeasure M μ0 π n).map (fun (h : MDPTrajectory S A n) (t : Fin m) ↦
        h (Fin.castLE hmn t))
      = mdpMeasure M μ0 π m := by
  show (mdpMeasure M μ0 π n).map (restrictTraj hmn) = _
  induction n with
  | zero =>
      obtain rfl : m = 0 := Nat.le_zero.mp hmn
      have : restrictTraj (S := S) (A := A) hmn = id := by
        funext h t
        exact absurd t.2 (Nat.not_lt_zero _)
      rw [this, Measure.map_id]
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hm | hm
      · have hmn' : m ≤ n := Nat.lt_succ_iff.mp hm
        have hcomp : restrictTraj (S := S) (A := A) hmn
            = (restrictTraj hmn') ∘ (fun h : MDPTrajectory S A (n + 1) ↦ Fin.init h) := by
          funext h t
          rfl
        have hinit : Measurable (fun h : MDPTrajectory S A (n + 1) ↦ Fin.init h) := by
          rw [measurable_pi_iff]
          exact fun t ↦ measurable_pi_apply _
        rw [hcomp, ← Measure.map_map (measurable_restrictTraj hmn') hinit,
          map_init, ih hmn']
      · obtain rfl : m = n + 1 := le_antisymm hmn hm
        have : restrictTraj (S := S) (A := A) hmn = id := by
          funext h t
          rfl
        rw [this, Measure.map_id]
