-- Prove2me | solution 1 for KServer.workFnU_isometry_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T17:40:55.487463+00:00
-- url     : https://prove2.me/submissions/4fa7ad97-3c1e-4ab0-9752-ba5b8e60664c

import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFn_rec_le
import Theorems.Thm_KServer_workFn_rec_ge

set_option autoImplicit false
open KServer

private lemma work_nil (k : ℕ) (M : Type) [MetricSpace M]
    (C X : Config k M) : workFn C [] X = moveCost C X := by
  unfold workFn
  have hs : {c : ℝ | ∃ S : ℕ → Config k M, ServesFrom C [] S ∧
      c = (∑ j ∈ Finset.range ([] : List M).length, moveCost (S j) (S (j + 1)))
        + moveCost (S ([] : List M).length) X} = {moveCost C X} := by
    ext c
    constructor
    · rintro ⟨S, hS, rfl⟩
      simp [hS.1]
    · intro hc
      obtain rfl := Set.mem_singleton_iff.mp hc
      exact ⟨fun _ => C, ⟨rfl, fun j => Fin.elim0 j⟩, by simp⟩
  rw [hs, csInf_singleton]

private lemma map_update (k : ℕ) (M N : Type) (e : M → N)
    (X : Config k M) (i : Fin k) (r : M) :
    (fun j => e (Function.update X i r j)) =
      Function.update (fun j => e (X j)) i (e r) := by
  classical
  funext j
  by_cases h : j = i
  · subst j
    simp
  · rw [Function.update_of_ne h, Function.update_of_ne h]

private lemma work_embedding (k : ℕ) (hk : 1 ≤ k) (M N : Type)
    [MetricSpace M] [MetricSpace N] (e : M → N)
    (he : ∀ x y, dist (e x) (e y) = dist x y)
    (C : Config k M) (σ : List M) (X : Config k M) :
    workFn (fun i => e (C i)) (σ.map e) (fun i => e (X i)) = workFn C σ X := by
  classical
  induction σ using List.reverseRecOn generalizing X with
  | nil => simp only [List.map_nil, work_nil, moveCost, he]
  | @append_singleton σ r ih =>
    simp only [List.map_append, List.map_singleton]
    apply le_antisymm
    · obtain ⟨i, hi⟩ := KServer.workFn_rec_ge k hk M C σ r X
      have h := KServer.workFn_rec_le k hk N (fun j => e (C j))
        (σ.map e) (e r) (fun j => e (X j)) i
      rw [← map_update, ih, he] at h
      exact h.trans hi
    · obtain ⟨i, hi⟩ := KServer.workFn_rec_ge k hk N (fun j => e (C j))
        (σ.map e) (e r) (fun j => e (X j))
      rw [← map_update, ih, he] at hi
      exact (KServer.workFn_rec_le k hk M C σ r X i).trans hi

theorem solution (k : ℕ) (hk : 1 ≤ k) (M N : Type)
    [MetricSpace M] [MetricSpace N] (e : M → N)
    (he : ∀ x y, dist (e x) (e y) = dist x y)
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    workFnU (fun i => e (C₀ i)) (σ.map e) (fun i => e (X i)) =
      workFnU C₀ σ X := by
  unfold workFnU
  apply iInf_congr
  intro π
  exact work_embedding k hk M N e he C₀ σ (X ∘ π)

#print axioms solution
