-- Prove2me | Theorems.Thm_Couret_properSupport_map_iff
-- name    : Couret.properSupport_map_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:16.089208+00:00
-- url     : https://prove2.me/theorems/dd559824-f840-461c-b6e8-b9ca35e1086c
-- title:
--   Proper product support commutes with reduction modulo 30
-- statement:
--   Let $w$ be a finite word of natural numbers each coprime to 30, and let $u$ code a unit residue $r(u)$. Then
--
--   $$u\text{ is a proper selected product of the encoded word}\Longleftrightarrow\exists d:\ d\text{ is a proper selected product of }w,\quad d\bmod30=r(u).$$
--
--   A proper selection picks at least one occurrence and omits at least one. This transports exact proper-support semantics without a primality assumption.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ModularDivisorBridge.lean, lines 143–160; source file SHA-256 f72e04425efd9d90f42cc1765e52bcd661653cc739601fb88631de6f94f69c41; theorem Couret.properSupport_map_iff

import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316
import Std
import Theorems.Thm_Couret_decode_encode30
import Theorems.Thm_Couret_mul30_residue
import Theorems.Thm_Couret_residue30_injective
import Definitions.Def_Couret_DivisorCompleteness_e4011d047800

/-!
COU-87 S2M, 2026-10-30: the exact bridge from natural divisors to the
eight-letter modulo-30 automaton. Prime occurrences need not be distinct.
No finite 147-state / 101-class table is imported here.
-/

universe v
namespace Couret



namespace Choice











end Choice

theorem properSupport_map_iff (w : Word Nat) (hw : w.coprime30Factors) (u : Code30) :
    properSupport mod30Product (w.map encode30) u ↔
      ∃ d : Nat, properSupport natProduct w d ∧ d % 30 = residue30 u := by sorry


















end Couret
