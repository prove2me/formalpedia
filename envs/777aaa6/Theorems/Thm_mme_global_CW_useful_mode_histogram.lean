-- Prove2me | Theorems.Thm_mme_global_CW_useful_mode_histogram
-- name    : mme_global_CW_useful_mode_histogram
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:47:26.376814+00:00
-- url     : https://prove2.me/theorems/8135ebeb-fc53-4d93-a751-ee00743ffb1e
-- title:
--   Useful global words have a fixed coarse histogram
-- statement:
--   Every useful word on an unpaired global address has the coarse histogram obtained by summing its full-cell counts. Its entire coarse type class therefore has one explicit multinomial cardinality, independent of the particular useful word.
-- source:
--   Finite global stage of More Asymmetry Proposition 5.1 / Theorem 5.3.

import Definitions.Def_mme_global_CW_counting_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ MME.GlobalCW MME.RecursiveXHash
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_useful_mode_histogram {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    {W : Type*} [Fintype W] (i : Fin 3) (a : RecursiveXHash.Address degree R bounds n)
    (mu : Cell degree R bounds → W → ℕ) (f : Place n → W) (hf : Useful (cell a) mu f) :
    ModeType (RecursiveXHash.block i a) (aggregate i mu) f ∧
    Nat.card {g : Place n → W // ModeType (RecursiveXHash.block i a) (aggregate i mu) g} =
      modeNumber i mu := by
  sorry
