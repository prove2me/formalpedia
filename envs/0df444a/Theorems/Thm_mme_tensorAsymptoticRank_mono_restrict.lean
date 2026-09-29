-- Prove2me | Theorems.Thm_mme_tensorAsymptoticRank_mono_restrict
-- name    : mme_tensorAsymptoticRank_mono_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:22:27.044613+00:00
-- url     : https://prove2.me/theorems/6dd860db-1821-4ad6-8d95-c23d5dd7979b
-- title:
--   Asymptotic tensor rank is monotone under restriction
-- statement:
--   Let $X$ and $Y$ be order-three tensors over a field $K$. If $X$ is a restriction of $Y$, then asymptotic tensor rank is monotone:
--
--   $$\widetilde R(X) \le \widetilde R(Y).$$
--
--   This is the restriction-monotonicity principle needed to compare a direct sum extracted by the laser method with the tensor power from which it was obtained.
-- source:
--   V. Strassen, The asymptotic spectrum of tensors, Journal für die reine und angewandte Mathematik 384 (1988), 102–152; restriction monotonicity of spectral points and the dual characterization of asymptotic rank.

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_duality
open MME
universe u

theorem mme_tensorAsymptoticRank_mono_restrict
    {K : Type u} [Field K] {X Y : TensorObj K 3}
    (h : TensorObj.Restrict X Y) :
    tensorAsymptoticRank X ≤ tensorAsymptoticRank Y := by sorry
