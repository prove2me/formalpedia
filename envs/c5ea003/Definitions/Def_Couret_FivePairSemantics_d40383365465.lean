-- Prove2me | Definitions.Def_Couret_FivePairSemantics_d40383365465
-- name    : Couret_FivePairSemantics_d40383365465
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:45.979995+00:00
-- url     : https://prove2.me/theorems/d2f41b24-7a7f-4b64-a6d1-fe382e7d5e56
-- title:
--   Factor-pair and mask-pair predicates for 64141
-- statement:
--   For unit-residue codes $a,b$ modulo 30, the factor-pair predicate asks for $d,e>1$ with $de=64141$, residues $a,b$, and the prescribed bit-index ordering. The mask-pair predicate asks for the same ordering, both codes present in mask 254, and code product equal to the identity.
--
--   These definitions isolate the arithmetic and finite-mask descriptions whose equivalence is proved separately. Mask 254 has every unit-residue bit except the identity bit.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/FivePairSemantics.lean; source file SHA-256 8b2d02904e438e1da57317890d439cece1022f7fb4ad1cbb929067cc80c7fde2

import Std
import Definitions.Def_Couret_OptimalFive_2f3f11b1b6a3
namespace Couret
namespace S5

/- The cancellation/complement argument follows the archived S4 proof,
   specialized here to the explicit five-prime counterexample. -/
def factorPair64141 (a b : Code30) : Prop :=
  ∃ d e : Nat, 1 < d ∧ 1 < e ∧ d * e = 64141 ∧
    d % 30 = residue30 a ∧ e % 30 = residue30 b ∧ bitIndex30 a ≤ bitIndex30 b

def maskPair64141 (a b : Code30) : Prop :=
  bitIndex30 a ≤ bitIndex30 b ∧ maskSupport 254 a ∧ maskSupport 254 b ∧ mul30 a b = (0,0)















end S5
end Couret


