-- Prove2me | Theorems.Thm_Couret_Certificate_arithmeticPair_iff_factorPair
-- name    : Couret.Certificate.arithmeticPair_iff_factorPair
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:48:10.118577+00:00
-- url     : https://prove2.me/theorems/86e8c071-0c24-46d3-9d4d-22ff2bf2ecbb
-- title:
--   Residue-compatible divisor pairs are factor pairs
-- statement:
--   Let $n\in\mathbb N$ satisfy $\gcd(n,30)=1$, and let $a,b\in\{0,\ldots,7\}$ index the unit residues $r=(1,7,11,13,17,19,23,29)$. The following are equivalent:
--
--   $$\begin{aligned}&a\le b,\quad r_a r_b\equiv n\pmod{30},\quad\text{each of }r_a,r_b\text{ occurs as a divisor residue for }1<d<n;\\ &\exists d,e>1:\ de=n,\quad d\equiv r_a\pmod{30},\quad e\equiv r_b\pmod{30},\quad a\le b.\end{aligned}$$
--
--   This identifies the arithmetic pair predicate with genuine complementary factor residues.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/CertificateProofs.lean, lines 149–186; source file SHA-256 34105504de63d99f05e7d3427ba82853380bac1d8c053b618776cd7d98da83b2; theorem Couret.Certificate.arithmeticPair_iff_factorPair

import Definitions.Def_Couret_CertificateProofs_3244eb90a0e1
import Std
import Theorems.Thm_Couret_coprime30_of_dvd
import Theorems.Thm_Couret_decode_encode30
import Theorems.Thm_Couret_mul30_residue
import Theorems.Thm_Couret_residue30_injective
import Definitions.Def_Couret_CertificateData_653c7a96c17c

/-! Universal consequences of the finite certificate checks. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate

theorem arithmeticPair_iff_factorPair (n : Nat) (hc : Nat.gcd n 30 = 1) (a b : Symbol) :
    arithmeticPair n a b ↔ factorPair n a b := by sorry




































end Certificate
end Couret
