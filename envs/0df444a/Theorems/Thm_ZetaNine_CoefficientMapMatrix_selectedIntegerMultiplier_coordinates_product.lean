-- Prove2me | Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_coordinates_product
-- name    : ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates_product
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-04T13:44:27.279434+00:00
-- url     : https://prove2.me/theorems/134e564c-4327-43b0-9ecd-e7d08fa133ec
-- title:
--   The actual selected rational multiplier has row inverse coordinates
-- statement:
--   For every even n>=2 and integers b,a, the actual inverse multiplier for the output (b,0,0,0,a) has rational quartic coordinates equal to (b,a) times the actual selection matrix S times the actual F inverse. No integer polynomial inverse or integral coefficient claim is made.
-- source:
--   Actual frozen native CoefficientMapMatrix source SHA256 a4bf1766c8bbcc1f2f83af27594ba10b3dfcd4e55058f10ccc4d4b25cb9c6d99

import Definitions.Def_ZetaNine_CoefficientMapMatrix

set_option autoImplicit false
open scoped BigOperators Matrix
open Polynomial ZetaNine ZetaNine.CoefficientMapMatrix ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapKernelBridge

theorem ZetaNine.CoefficientMapMatrix.selectedIntegerMultiplier_coordinates_product (n : ℕ) (hn2 : 2 ≤ n)
    (hn : Even n) (b a : ℤ) :
    polynomialCoordinates (selectedIntegerMultiplier n hn2 hn b a) =
      selectedIntegerPair b a ᵥ* (selectionMatrix * (actualFMatrix n)⁻¹):= by sorry
