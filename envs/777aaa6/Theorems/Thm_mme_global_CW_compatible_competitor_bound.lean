-- Prove2me | Theorems.Thm_mme_global_CW_compatible_competitor_bound
-- name    : mme_global_CW_compatible_competitor_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:49:12.020856+00:00
-- url     : https://prove2.me/theorems/5b0f80d3-dc6e-400a-8fa0-4c4a9b7917b8
-- title:
--   Uniform compatible-competitor bound for global CW blocks
-- statement:
--   For a fixed coarse mode word and exact word histogram, the number of compatible global target addresses times the word-type cardinality is bounded by the full target-fiber size times the explicit compatibility multinomial count. The proof is an orbit-symmetry double count on unpaired positions.
-- source:
--   Finite global stage of More Asymmetry Proposition 5.1 / Theorem 5.3.

import Definitions.Def_mme_global_CW_counting_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ MME.GlobalCW MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_compatible_competitor_bound {half R : ℕ} {W G : Type*} [Fintype W] [Fintype G]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (i : Fin 3) (y : ∀ r, Fin (n r) → Fin (half + 1))
    (eta : Fin R → Fin (half + 1) → W → ℕ)
    (boundary : Cell half R parent → Prop) (group : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2)
    (f : Place n → W) (hf : ModeType y eta f) :
    ((MME.RecursiveXHash.target (n := n) m).filter (fun a ↦
        MME.RecursiveXHash.block i a = y ∧
          Compatible (cell a) boundary group mu f)).card *
        Nat.card {g : Place n → W // ModeType y eta g} ≤
      ((MME.RecursiveXHash.target (n := n) m).filter
        (fun a ↦ MME.RecursiveXHash.block i a = y)).card *
          compatibilityNumber boundary group mu := by
  sorry
