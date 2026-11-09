-- Prove2me | Theorems.Thm_Couret_fullSupport_map_iff
-- name    : Couret.fullSupport_map_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:30.422243+00:00
-- url     : https://prove2.me/theorems/50af9938-135f-4304-8662-4518686d1074
-- title:
--   Full product support commutes with reduction modulo 30
-- statement:
--   Let $w$ be a finite word of natural numbers each coprime to 30, and let $u$ code a unit residue $r(u)$. Then
--
--   $$u\text{ occurs as a selected product after encoding }w\Longleftrightarrow\exists d:\ d\text{ is a selected product of }w,\quad d\bmod30=r(u).$$
--
--   Selections may be empty or full; no primality assumption is required.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ModularDivisorBridge.lean, lines 128–141; source file SHA-256 f72e04425efd9d90f42cc1765e52bcd661653cc739601fb88631de6f94f69c41; theorem Couret.fullSupport_map_iff

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

theorem fullSupport_map_iff (w : Word Nat) (hw : w.coprime30Factors) (u : Code30) :
    fullSupport mod30Product (w.map encode30) u ↔
      ∃ d : Nat, fullSupport natProduct w d ∧ d % 30 = residue30 u := by sorry




















end Couret
