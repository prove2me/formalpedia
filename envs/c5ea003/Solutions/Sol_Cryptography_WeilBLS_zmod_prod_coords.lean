-- Prove2me | solution 1 for Cryptography.WeilBLS.zmod_prod_coords
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T23:33:04.437633+00:00
-- url     : https://prove2.me/submissions/e3a44ed1-ffe3-4744-8b2a-0fba3d9ff4ed

import Mathlib
import Definitions.Def_Cryptography_WeilPairingBLS
import Definitions.Def_Cryptography_WeilPairingDeterminant

open scoped BigOperators

theorem solution {n : ℕ} [NeZero n] (w : ZMod n × ZMod n) :
    ((w.1.val : ℤ) • ((1 : ZMod n), (0 : ZMod n)) +
      (w.2.val : ℤ) • ((0 : ZMod n), (1 : ZMod n))) = w := by
  ext <;> simp [zsmul_eq_mul]

#print axioms solution
