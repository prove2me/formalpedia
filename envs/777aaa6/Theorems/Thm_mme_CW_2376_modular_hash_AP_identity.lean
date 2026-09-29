-- Prove2me | Theorems.Thm_mme_CW_2376_modular_hash_AP_identity
-- name    : mme_CW_2376_modular_hash_AP_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T20:04:57.138781+00:00
-- url     : https://prove2.me/theorems/1042e800-4f5b-4196-b3b1-5b0152483e36
-- title:
--   Odd-modulus CW profile hashes form an arithmetic progression
-- statement:
--   For an odd modulus $M$, let $x,y,z$ be five-grade profile addresses whose mixed triple is supported coordinatewise. Their ordinary affine hash labels in $\mathbb Z/M\mathbb Z$ satisfy
--
--   $$
--   H_X(x)+H_Y(y)=2H_Z(z).
--   $$
--
--   Oddness makes two invertible, so this follows by dividing the doubled progression identity by two. The result is the precise modular relation needed to invoke a lower-half three-term-progression-free no-collision lemma.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), outer square-profile hashes on journal p. 268 and progression identity (6) on pp. 259--260; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_modular_hash
import Theorems.Thm_mme_CW_2376_doubled_hash_AP_identity

open MME

theorem mme_CW_2376_modular_hash_AP_identity
    {M m : ℕ} (hM : Odd M)
    (b0 : ZMod M) (w : Fin (cw2376ProfileLength m) → ZMod M)
    (x y z : CW2376ProfileAddress m)
    (hsupp : CW2376CoordinatewiseSupported
      (cw2376MixedAddress x y z)) :
    cw2376XHashMod w (x 0) + cw2376YHashMod b0 w (y 1) =
      2 * cw2376ZHashMod b0 w (z 2) := by
  sorry
