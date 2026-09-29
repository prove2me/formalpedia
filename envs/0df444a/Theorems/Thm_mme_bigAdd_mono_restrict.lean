-- Prove2me | Theorems.Thm_mme_bigAdd_mono_restrict
-- name    : mme_bigAdd_mono_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:30:15.2495+00:00
-- url     : https://prove2.me/theorems/00651442-1945-4ac4-80ab-0b38aee18eb6
-- title:
--   Finite direct sums preserve tensor restriction componentwise
-- statement:
--   Let $(X_j)_{j<k}$ and $(Y_j)_{j<k}$ be finite families of order-$d$ tensors over a field $K$. If $X_j$ is a restriction of $Y_j$ for every index $j$, then their direct sums satisfy
--
--   $$
--   \bigoplus_{j<k}X_j\;\leq_{\mathrm{Restrict}}\;\bigoplus_{j<k}Y_j.
--   $$
--
--   The witnessing maps are the modewise direct sums of the component restriction maps. This functoriality is the algebraic step that converts a mode-disjoint family of laser-method survivors into a direct sum of their matrix-multiplication restrictions.
-- source:
--   Standard functoriality of finite direct sums under modewise linear tensor restriction; used in the direct-sum assembly on D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 271 (PDF p. 21); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_tensor_quotient
open MME
universe u

theorem mme_bigAdd_mono_restrict
    {K : Type u} [Field K] {d k : ℕ}
    {X Y : Fin k → TensorObj K d}
    (h : ∀ j, TensorObj.Restrict (X j) (Y j)) :
    TensorObj.Restrict (TensorObj.bigAdd X) (TensorObj.bigAdd Y) := by sorry
