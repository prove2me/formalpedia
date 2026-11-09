-- Prove2me | Theorems.Thm_Couret_properSupport_mod30_iff_divisor
-- name    : Couret.properSupport_mod30_iff_divisor
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:04:21.886135+00:00
-- url     : https://prove2.me/theorems/4f241b60-eb27-435b-8147-5f4635dbafb1
-- title:
--   Proper residue subproducts represent strict divisor residues
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. Let $w$ be a word of natural primes with product $n$ coprime to 30. For every $u\in C$,
--
--   $$u\in U_{\rm proper}(\operatorname{encode}_{30}(w))\iff\exists d\mid n,\ 1<d<n,\ d\bmod30=\rho(u).$$
--
--   Both nonemptiness and omission are required of the selection.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ModularDivisorBridge.lean, lines 173–184; source file SHA-256 f72e04425efd9d90f42cc1765e52bcd661653cc739601fb88631de6f94f69c41; theorem Couret.properSupport_mod30_iff_divisor

import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316
import Std
import Theorems.Thm_Couret_coprime30_of_dvd
import Theorems.Thm_Couret_properSupport_iff_nontrivial_divisor
import Theorems.Thm_Couret_properSupport_map_iff
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

theorem properSupport_mod30_iff_divisor (w : Word Nat) (hp : w.primeFactors)
    (hc : Nat.gcd (total natProduct w) 30 = 1) (u : Code30) :
    properSupport mod30Product (w.map encode30) u ↔
      ∃ d : Nat, d ∣ total natProduct w ∧ 1 < d ∧ d < total natProduct w ∧
        d % 30 = residue30 u := by sorry














end Couret
