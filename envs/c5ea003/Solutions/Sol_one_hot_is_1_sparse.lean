-- Prove2me | solution 1 for one_hot_is_1_sparse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-14T01:15:08.046993+00:00
-- url     : https://prove2.me/submissions/9c91dfb1-7888-4037-8f4c-f269be7db0f8

-- Sol generated from MachineLearning/QuantumTransformer/BiologicalCrystallization.lean
import Mathlib
import Definitions.Def_MachineLearning_QuantumTransformer_BiologicalCrystallization

/-! # CatalogBuild.MachineLearning.QuantumTransformer.BiologicalCrystallization

Auto-generated from theorem catalog database.
Domain: MachineLearning/QuantumTransformer
Declarations: 13
-/


noncomputable section






















































theorem solution{n : ℕ} (v : Fin n → ℝ) (hv : is_one_hot v) :
    is_k_sparse 1 v := by
  unfold is_k_sparse
  obtain ⟨k, hk1, hk0⟩ := hv
  calc (Finset.univ.filter (fun i => v i ≠ 0)).card
      ≤ ({k} : Finset (Fin n)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        simp only [Finset.mem_singleton]
        by_contra h
        exact hi (hk0 i h)
    _ = 1 := Finset.card_singleton k
