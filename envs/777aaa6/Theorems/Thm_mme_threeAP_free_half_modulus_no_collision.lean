-- Prove2me | Theorems.Thm_mme_threeAP_free_half_modulus_no_collision
-- name    : mme_threeAP_free_half_modulus_no_collision
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T19:41:30.402787+00:00
-- url     : https://prove2.me/theorems/89e7e8ed-cc3f-4248-bf0d-205718edde5a
-- title:
--   A progression-free lower half has no modular hash collisions
-- statement:
--   Let $S$ be a set of natural-number representatives contained in the lower half of a modulus $M$, and assume $S$ has no nontrivial three-term arithmetic progression. If $a,b,c\in S$ satisfy
--
--   $$
--   a+c\equiv 2b\pmod M,
--   $$
--
--   then $a=b=c$. Since $a+c<M$ and $2b<M$, the modular equality cannot wrap around and is therefore an ordinary natural-number equality. This is the precise bridge from the modular CW hash to a standard finite progression-free set.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 257: the Salem–Spencer representatives are chosen below M/2 so that modular three-term progressions do not wrap; https://doi.org/10.1016/S0747-7171(08)80013-2. Ordinary no-collision input: Prove2Me theorem mme_3AP_free_no_collision.

import Mathlib.Data.ZMod.Basic
import Theorems.Thm_mme_3AP_free_no_collision

theorem mme_threeAP_free_half_modulus_no_collision
    (M : ℕ) (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range (M / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (a b c : ℕ) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hmod : (a : ZMod M) + (c : ZMod M) = 2 * (b : ZMod M)) :
    a = b ∧ b = c := by sorry
