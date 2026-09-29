-- Prove2me | Definitions.Def_mme_CW_2376_hash_arithmetic
-- name    : mme_CW_2376_hash_arithmetic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T19:55:25.440287+00:00
-- url     : https://prove2.me/theorems/c7b8352e-8d29-4dcb-ac9e-50fe9b5f02ac
-- title:
--   Doubled affine hashes for the outer CW 2.376 profile
-- statement:
--   For five-grade words of length $N$, introduce the doubled affine hashes used in the outer Coppersmith--Winograd square pruning. With affine offset $b_0$ and position weights $w_j$, they are
--
--   $$
--   H_X^{(2)}=2\sum_j I_jw_j,\qquad H_Y^{(2)}=2b_0+2\sum_jJ_jw_j,\qquad H_Z^{(2)}=b_0+\sum_j(4-K_j)w_j.
--   $$
--
--   The asymmetric placement of $b_0$ is the source construction: it preserves the progression identity and supplies the independent affine randomness used in collision counting. Doubling postpones division by two until specialization to an odd modulus. These definitions contain no probabilistic or tensor assertion.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), outer square-profile affine hashes on journal p. 268, with equation (6) on pp. 259--260; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_mme_CW_2376_profile_induced_family

open BigOperators

namespace MME

def cw2376DoubledXHash
    {R : Type} [CommSemiring R] {N : ℕ}
    (w : Fin N → R) (x : Fin N → Fin 5) : R :=
  ∑ j, ((2 * (x j).val : ℕ) : R) * w j

def cw2376DoubledYHash
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin N → R) (y : Fin N → Fin 5) : R :=
  2 * b0 + ∑ j, ((2 * (y j).val : ℕ) : R) * w j

def cw2376DoubledZHash
    {R : Type} [CommSemiring R] {N : ℕ}
    (b0 : R) (w : Fin N → R) (z : Fin N → Fin 5) : R :=
  b0 + ∑ j, ((4 - (z j).val : ℕ) : R) * w j

end MME


