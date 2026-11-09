-- Prove2me | Theorems.Thm_Couret_S5_six_for_factorization
-- name    : Couret.S5.six_for_factorization
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:53:01.256573+00:00
-- url     : https://prove2.me/theorems/2c52fa72-4e1e-4129-8f2e-2d1e9638b747
-- title:
--   Six prime factors make every divisor residue proper
-- statement:
--   Let $w$ be a word of natural primes with product $n$, at least six positions, and $\gcd(n,30)=1$. For every unit residue code $u$, $$\exists d\mid n,\ d\equiv u\pmod{30}\iff\exists d\mid n,\ 1<d<n,\ d\equiv u\pmod{30}.$$ Prime factors are counted with multiplicity; the residue symbol denotes the integer residue represented by the code.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/DavenportThreshold.lean, lines 92–97; source file SHA-256 c800425f72bd7cac263232227e182bea9d8881d436ee30021d29b43628c45e05; theorem Couret.S5.six_for_factorization

import Definitions.Def_Couret_DavenportThreshold_ac37b2f8de8c
import Std
import Theorems.Thm_Couret_S5_full_equals_proper_of_six
import Theorems.Thm_Couret_fullSupport_mod30_iff_divisor
import Theorems.Thm_Couret_properSupport_mod30_iff_divisor
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
namespace Couret
namespace S5

theorem six_for_factorization (w : Word Nat) (hp : w.primeFactors) (n : Nat)
    (hn : total natProduct w = n) (hc : Nat.gcd n 30 = 1) (hw : 6 ≤ length w) :
    ∀ u : Code30, (∃ d : Nat, d ∣ n ∧ d % 30 = residue30 u) ↔
      ∃ d : Nat, d ∣ n ∧ 1 < d ∧ d < n ∧ d % 30 = residue30 u := by sorry


end S5
end Couret
