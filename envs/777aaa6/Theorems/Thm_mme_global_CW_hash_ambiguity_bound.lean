-- Prove2me | Theorems.Thm_mme_global_CW_hash_ambiguity_bound
-- name    : mme_global_CW_hash_ambiguity_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:51:36.510556+00:00
-- url     : https://prove2.me/theorems/b036dc4f-f045-449c-aa16-b9c6162b13de
-- title:
--   Global compatible-collision hash incidence bound
-- statement:
--   The number of hash states retaining a target together with a distinct compatible target sharing Y or Z, multiplied by the fixed coarse-word type cardinality, is bounded by the target-fiber count times the explicit compatibility count and the shared-pair affine hash bound.
-- source:
--   Finite global stage of More Asymmetry Proposition 5.1 / Theorem 5.3.

import Definitions.Def_mme_global_CW_counting_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ MME.GlobalCW MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_hash_ambiguity_bound {half R N p : ℕ} [Fact p.Prime]
    {W G : Type*} [Fintype W] [Fintype G]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r)) (S : Finset (ZMod p))
    (hgrade : half < p) (i : Fin 3) (hi : i = 1 ∨ i = 2)
    (a : MME.RecursiveYZ.Address half R parent n) (ha : a ∈ target m)
    (eta : Fin R → Fin (half + 1) → W → ℕ)
    (boundary : Cell half R parent → Prop) (group : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2)
    (f : Place n → W) (hf : ModeType (block i a) eta f) :
    (Finset.univ.filter (fun q : (Fin (N + 2) → ZMod p) × ZMod p ↦
      a ∈ hashed m e S q ∧ ∃ b ∈ target m,
        block i b = block i a ∧ Compatible (cell b) boundary group mu f ∧
          b ≠ a ∧ b ∈ hashed m e S q)).card *
      Nat.card {g : Place n → W // ModeType (block i a) eta g} ≤
    ((target (n := n) m).filter (fun b ↦ block i b = block i a)).card *
      compatibilityNumber boundary group mu * S.card * p ^ N := by
  sorry
