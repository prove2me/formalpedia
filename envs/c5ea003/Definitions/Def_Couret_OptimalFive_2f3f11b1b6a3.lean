-- Prove2me | Definitions.Def_Couret_OptimalFive_2f3f11b1b6a3
-- name    : Couret_OptimalFive_2f3f11b1b6a3
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:25.195265+00:00
-- url     : https://prove2.me/theorems/9262ab37-ddb2-4307-9a2c-f309f5ce2b70
-- title:
--   Five-prime witness and residue-pair enumeration
-- statement:
--   The witness word is the labeled prime-occurrence list $(7,7,7,11,17)$, with product 64141. Given a total residue $r$ and a natural mask $m$, the pair enumerator scans the fixed Python residue order and returns residue pairs $(a,b)$ in bit-index order whose two bits are present and whose product code equals $r$.
--
--   This packages the concrete optimality witness and its finite residue-pair output interface.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/OptimalFive.lean; source file SHA-256 10e4872f2ae446d57ad6e2c526d92085da7cdb70df9bb99e2641c0da1b7e7c1f

import Std
import Definitions.Def_Couret_DavenportThreshold_ac37b2f8de8c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

def fivePrimes : Word Nat := .snoc (.snoc (.snoc (.snoc (.snoc .empty 7) 7) 7) 11) 17




























def pairList (r : Code30) (mask : Nat) : List (Nat × Nat) :=
  pythonAlphabet.flatMap (fun a =>
    (pythonAlphabet.filter (fun b => decide (bitIndex30 a ≤ bitIndex30 b ∧
      maskSupport mask a ∧ maskSupport mask b ∧ mul30 a b = r))).map
        (fun b => (residue30 a,residue30 b)))







end S5
end Couret


