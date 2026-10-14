-- Prove2me | solution 1 for KServer.workFnU_initial_stability
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T23:13:01.278787+00:00
-- url     : https://prove2.me/submissions/51e8b0fc-c293-4eef-be02-a8919cbc61b7

import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge
import Theorems.Thm_KServer_workFn_nil
import Theorems.Thm_KServer_workFn_approx_offlineCost
import Theorems.Thm_KServer_offlineCost_le_workFn

set_option autoImplicit false
open KServer

private lemma work_initial_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (A B : Config k M) (σ : List M) (X : Config k M) :
    workFn A σ X ≤ workFn B σ X + moveCost A B := by
  classical
  induction σ using List.reverseRecOn generalizing X with
  | nil =>
    rw [workFn_nil k hk, workFn_nil k hk]
    unfold moveCost
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by simpa [add_comm] using dist_triangle (A i) (B i) (X i)
  | @append_singleton σ r ih =>
    obtain ⟨i, hi⟩ := workFn_rec_ge k hk M B σ r X
    have hl := workFn_rec_le k hk M A σ r X i
    have hm := ih (Function.update X i r)
    linarith

private lemma unordered_initial_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (A B : Config k M) (σ : List M) (X : Config k M) :
    workFnU A σ X ≤ workFnU B σ X + moveCost A B := by
  classical
  have hn : Nonempty (Equiv.Perm (Fin k)) := ⟨Equiv.refl _⟩
  obtain ⟨π, hπ⟩ := Finite.exists_min (fun π : Equiv.Perm (Fin k) => workFn B σ (X ∘ π))
  have hB : workFnU B σ X = workFn B σ (X ∘ π) := by
    unfold workFnU
    apply le_antisymm
    · exact ciInf_le (Finite.bddBelow_range _) π
    · exact le_ciInf hπ
  rw [hB]
  exact (ciInf_le (Finite.bddBelow_range _) π).trans (work_initial_le k hk M A B σ (X ∘ π))

private lemma offline_initial_le (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (A B : Config k M) (σ : List M) :
    offlineCost A σ ≤ offlineCost B σ + moveCost A B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨X, hX⟩ := workFn_approx_offlineCost k hk M B σ ε hε
  have h := work_initial_le k hk M A B σ X
  have hA := offlineCost_le_workFn k hk M A σ X
  linarith

theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (A B : Config k M) (σ : List M) :
    (∀ X : Config k M, |workFnU A σ X - workFnU B σ X| ≤ moveCost A B) ∧
      |offlineCost A σ - offlineCost B σ| ≤ moveCost A B := by
  have hsym : moveCost B A = moveCost A B := by simp [moveCost, dist_comm]
  constructor
  · intro X
    have hAB := unordered_initial_le k hk M A B σ X
    have hBA := unordered_initial_le k hk M B A σ X
    rw [hsym] at hBA
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hAB := offline_initial_le k hk M A B σ
    have hBA := offline_initial_le k hk M B A σ
    rw [hsym] at hBA
    exact abs_le.mpr ⟨by linarith, by linarith⟩

#print axioms solution
