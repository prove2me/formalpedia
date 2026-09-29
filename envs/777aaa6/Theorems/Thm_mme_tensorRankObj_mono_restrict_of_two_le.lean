-- Prove2me | Theorems.Thm_mme_tensorRankObj_mono_restrict_of_two_le
-- name    : mme_tensorRankObj_mono_restrict_of_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:28:33.749896+00:00
-- url     : https://prove2.me/theorems/5501c4ff-3190-4e9e-803b-f9e4b26270a1
-- title:
--   Tensor rank is monotone under restriction
-- statement:
--   Let $X$ and $Y$ be tensors of order $d\ge2$ over a field $K$. If $X$ is a restriction of $Y$, then ordinary tensor rank is monotone:
--
--   $$
--   X\le Y\quad\Longrightarrow\quad R(X)\le R(Y).
--   $$
--
--   This is the concrete tensor-object form of rank monotonicity in Strassen's preorder and is used to bound every direct sum extracted from a tensor power.
-- source:
--   Standard monotonicity of tensor rank under modewise linear restriction; see Wigderson and Zuiddam, Asymptotic spectra: theory, applications and extensions, Definitions 2.4–2.5.

import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_spectrum
open MME
universe u

theorem mme_tensorRankObj_mono_restrict_of_two_le
    {K : Type u} [Field K] {d : ℕ}
    (hd : 1 < d) {X Y : TensorObj K d}
    (h : TensorObj.Restrict X Y) :
    tensorRankObj X ≤ tensorRankObj Y := by sorry
