-- Prove2me | Theorems.Thm_Couret_decode_encode30
-- name    : Couret.decode_encode30
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:51:33.660721+00:00
-- url     : https://prove2.me/theorems/a5278530-aa3f-4442-9f09-31e2236fd0f2
-- title:
--   Coprime natural numbers round-trip through the residue code
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. If $n\in\mathbb N$ and $\gcd(n,30)=1$, then
--
--   $$\rho(\operatorname{encode}_{30}(n))=n\bmod30.$$
--
--   The coprimality condition ensures the remainder belongs to the eight represented units.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ModularDivisorBridge.lean, lines 72–77; source file SHA-256 f72e04425efd9d90f42cc1765e52bcd661653cc739601fb88631de6f94f69c41; theorem Couret.decode_encode30

import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316
import Std
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

theorem decode_encode30 (n : Nat) (hn : Nat.gcd n 30 = 1) :
    residue30 (encode30 n) = n % 30 := by sorry


































end Couret
