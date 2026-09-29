-- Prove2me | Theorems.Thm_mme_CW_q6_hash_bucket_coherence
-- name    : mme_CW_q6_hash_bucket_coherence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:56:32.060275+00:00
-- url     : https://prove2.me/theorems/56fdc56c-13b4-4d2f-9100-bfb0577213aa
-- title:
--   Progression-free coupled q=6 hashes force one common bucket
-- statement:
--   Set $M=4X^2+1$, and let $S\subseteq[0,M/2)$ contain no nontrivial three-term arithmetic progression. Suppose the three modes of a supported mixed coupled $q=6$ address have doubled affine hashes $2s_X,2s_Y,2s_Z$ modulo $M$, with $s_X,s_Y,s_Z\in S$. Then
--
--   $$
--   s_X=s_Y=s_Z.
--   $$
--
--   Indeed, supportedness gives the modular progression relation and the odd modulus makes doubling cancellable. The lower-half condition then removes modular wraparound, so progression-freeness forces a single common bucket. This is the exact inducedness interface used before X/Y collision pruning.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 259–260 equation (6) and common-bucket conclusion, reused by the coupled q=6 hash on journal p. 271; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.Nat.Prime.Basic
import Theorems.Thm_mme_CW_q6_doubled_hash_AP_identity
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

open MME

theorem mme_CW_q6_hash_bucket_coherence
    (N Xcount : ℕ)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range ((4 * Xcount ^ 2 + 1) / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (b0 : ZMod (4 * Xcount ^ 2 + 1))
    (w : Fin (2 * N) → ZMod (4 * Xcount ^ 2 + 1))
    (x y z : CWQ6CoupledAddress N)
    (hsupp : CWQ6CoupledCoordinatewiseSupported
      (cwQ6CoupledMixedAddress x y z))
    (sx sy sz : ℕ) (hsx : sx ∈ S) (hsy : sy ∈ S) (hsz : sz ∈ S)
    (hx : cwQ6DoubledXHash b0 w (x 0) =
      2 * (sx : ZMod (4 * Xcount ^ 2 + 1)))
    (hy : cwQ6DoubledYHash b0 w (y 1) =
      2 * (sy : ZMod (4 * Xcount ^ 2 + 1)))
    (hz : cwQ6DoubledZHash b0 w (z 2) =
      2 * (sz : ZMod (4 * Xcount ^ 2 + 1))) :
    sx = sy ∧ sy = sz := by sorry
