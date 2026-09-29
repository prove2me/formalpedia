-- Prove2me | solution 1 for mme_released_global_sparse_marginals
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T11:31:48.61507+00:00
-- url     : https://prove2.me/submissions/79330bad-421b-40f8-9bef-9185e8efa4f5

import Definitions.Def_mme_released_global_profile_data
open BigOperators MME MME.ReleasedGlobal
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false

private theorem weighted_histogram_marginal {A V W : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq W] (f : A → V) (g : V → W)
    (l : List (A × ℕ)) (w : W) :
    (∑ v : V, if g v = w then
      (l.map (fun a ↦ if f a.1 = v then a.2 else 0)).sum else 0) =
      (l.map (fun a ↦ if g (f a.1) = w then a.2 else 0)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons,List.sum_cons,ite_add_zero,Finset.sum_add_distrib,ih]
    congr 1
    rw [Finset.sum_eq_single (f a.1)]
    · simp
    · intro v _ hv
      simp [Ne.symm hv]
    · simp

attribute [local irreducible] jointRows alpha atom rowCounts jointCounts coarseCounts wordCounts shapeEquiv

theorem solution (owner : Fin 6) (c : Shape) (i : Fin 3) (w : Word) :
    wordCounts owner i c w = alpha owner (shapeEquiv.symm c) *
      ((jointRows owner (shapeEquiv.symm c)).map
        (fun a ↦ if atom a.1 i = w then a.2 else 0)).sum := by
  unfold wordCounts jointCounts rowCounts
  have he (v : JointWord) :
      (if v i = w then alpha owner (shapeEquiv.symm c) *
        ((jointRows owner (shapeEquiv.symm c)).map (fun a ↦ if atom a.1 = v then a.2 else 0)).sum
        else 0) = alpha owner (shapeEquiv.symm c) *
        (if v i = w then
          ((jointRows owner (shapeEquiv.symm c)).map (fun a ↦ if atom a.1 = v then a.2 else 0)).sum
          else 0) := by
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.mul_sum]
  apply congrArg (fun n ↦ alpha owner (shapeEquiv.symm c)*n)
  exact weighted_histogram_marginal atom (fun v ↦ v i) (jointRows owner (shapeEquiv.symm c)) w
