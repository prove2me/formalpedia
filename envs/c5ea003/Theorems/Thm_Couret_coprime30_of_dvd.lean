-- Prove2me | Theorems.Thm_Couret_coprime30_of_dvd
-- name    : Couret.coprime30_of_dvd
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:57:09.80261+00:00
-- url     : https://prove2.me/theorems/d74178c8-6bb5-40e7-bf2d-a2bfee23320f
-- title:
--   Divisors retain coprimality with thirty
-- statement:
--   For natural $d,n$ with $d\mid n$ and $\gcd(n,30)=1$, $$\gcd(d,30)=1.$$ No separate positivity assumptions are needed.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ModularDivisorBridge.lean, lines 79–83; source file SHA-256 f72e04425efd9d90f42cc1765e52bcd661653cc739601fb88631de6f94f69c41; theorem Couret.coprime30_of_dvd

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

theorem coprime30_of_dvd {d n : Nat} (hd : d ∣ n)
    (hn : Nat.gcd n 30 = 1) : Nat.gcd d 30 = 1 := by sorry
































end Couret
