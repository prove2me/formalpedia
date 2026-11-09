-- Prove2me | Theorems.Thm_Couret_mod30_run_for_factorization
-- name    : Couret.mod30_run_for_factorization
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:37:50.300904+00:00
-- url     : https://prove2.me/theorems/9b83be7d-2e8c-434d-90b8-37e94b04d20a
-- title:
--   The modulo-30 run computes proper divisor residues
-- statement:
--   Let $w$ be a finite word of natural prime occurrences with total product $n>1$ and $\gcd(n,30)=1$. Encode every occurrence as a unit-residue code modulo 30. Then
--
--   $$\operatorname{run}(\operatorname{encode}(w))=\operatorname{active}\!\left(\operatorname{encode}(n),\ \{u:\exists d\mid n,\ 1<d<n,\ d\bmod30=r(u)\}\right).$$
--
--   This is exact divisor semantics, permitting repeated prime occurrences.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/ModularDivisorBridge.lean, lines 212–223; source file SHA-256 f72e04425efd9d90f42cc1765e52bcd661653cc739601fb88631de6f94f69c41; theorem Couret.mod30_run_for_factorization

import Definitions.Def_Couret_ModularDivisorBridge_2d9305253316
import Std
import Theorems.Thm_Couret_coprime30_of_dvd
import Theorems.Thm_Couret_decode_encode30
import Theorems.Thm_Couret_mul30_residue
import Theorems.Thm_Couret_properSupport_mod30_iff_divisor
import Theorems.Thm_Couret_residue30_injective
import Theorems.Thm_Couret_run_correct
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

theorem mod30_run_for_factorization (w : Word Nat) (hp : w.primeFactors)
    (n : Nat) (hn : total natProduct w = n) (hc : Nat.gcd n 30 = 1) (h1 : 1 < n) :
    run mod30Product (w.map encode30) = State.active (encode30 n) (fun u =>
      ∃ d : Nat, d ∣ n ∧ 1 < d ∧ d < n ∧ d % 30 = residue30 u) := by sorry








end Couret
