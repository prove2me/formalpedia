-- Prove2me | Theorems.Thm_mme_global_CW_exact_compatibility_card
-- name    : mme_global_CW_exact_compatibility_card
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:46:42.23535+00:00
-- url     : https://prove2.me/theorems/fc6a338c-bf82-46c4-9411-82abdddb88ea
-- title:
--   Exact global compatibility multinomial count
-- statement:
--   For an original global address of a fixed joint type, full cell profiles with matching masses have exactly the product-multinomial number of compatible words: boundary cells are prescribed individually and interior cells are aggregated by coarse mode.
-- source:
--   Finite global stage of More Asymmetry Proposition 5.1 / Theorem 5.3.

import Definitions.Def_mme_global_CW_counting_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ MME.GlobalCW MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_exact_compatibility_card {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    {W G : Type*} [Fintype W] [Fintype G]
    (m : ∀ r, RecursiveThinSplit.Split degree (bounds r) → ℕ)
    (a : RecursiveXHash.Address degree R bounds n) (ha : a ∈ RecursiveXHash.target m)
    (boundary : Cell degree R bounds → Prop) (group : Cell degree R bounds → G)
    (mu : Cell degree R bounds → W → ℕ) (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2) :
    Nat.card {f : Place n → W // Compatible (cell a) boundary group mu f} =
      compatibilityNumber boundary group mu := by
  sorry
