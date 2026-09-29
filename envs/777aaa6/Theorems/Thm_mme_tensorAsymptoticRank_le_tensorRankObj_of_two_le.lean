-- Prove2me | Theorems.Thm_mme_tensorAsymptoticRank_le_tensorRankObj_of_two_le
-- name    : mme_tensorAsymptoticRank_le_tensorRankObj_of_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:27:14.599018+00:00
-- url     : https://prove2.me/theorems/a8f58271-07b2-4023-92f1-01401722098d
-- title:
--   Asymptotic tensor rank is at most tensor rank
-- statement:
--   Let $X$ be a tensor of order $d\ge2$ over a field $K$. Its asymptotic tensor rank is bounded by its ordinary tensor rank:
--
--   $$
--   \widetilde R(X)\le R(X).
--   $$
--
--   Indeed, the defining infimum for asymptotic rank contains the first tensor power. The order assumption is the one required by the platform's concrete-to-quotient rank bridge.
-- source:
--   A direct consequence of the standard definition of asymptotic rank as the infimum of normalized ranks of positive tensor powers; see Wigderson and Zuiddam, Asymptotic spectra: theory, applications and extensions, Definition 2.8.

import Definitions.Def_mme_rank_bridge
open MME
universe u

theorem mme_tensorAsymptoticRank_le_tensorRankObj_of_two_le
    {K : Type u} [Field K] {d : ℕ}
    (hd : 1 < d) (X : TensorObj K d) :
    tensorAsymptoticRank X ≤ tensorRankObj X := by sorry
