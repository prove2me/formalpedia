-- Prove2me | Theorems.Thm_Couret_Certificate_factorization_T_certificate
-- name    : Couret.Certificate.factorization_T_certificate
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:07.837739+00:00
-- url     : https://prove2.me/theorems/1b81c7fb-d3c8-45d2-bad6-a8071b9f8e18
-- title:
--   A certificate state for every coprime prime factorization
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. Let $w$ be a word of natural primes with product $n>1$ and $\gcd(n,30)=1$. There is a state index $0\le i<147$ whose decoded total is the code of $n$ and whose decoded support is exactly the residues of divisors $d\mid n$ with $1<d<n$. Its tabulated output equals both its presence count and its mask output. For every pair of symbols $a,b\in\{0,\ldots,7\}$,
--
--   $$\operatorname{pairPresent}(i,a,b)\iff D_n(a)\land D_n(b)\land a\le b\land\rho(a)\rho(b)\equiv n\pmod {30},$$
--
--   where $D_n(a)$ means that some strict divisor of $n$ has the residue represented by symbol $a$. This connects arithmetic factorizations to the explicit finite-state table.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S4/CertificateProofs.lean, lines 188–205; source file SHA-256 34105504de63d99f05e7d3427ba82853380bac1d8c053b618776cd7d98da83b2; theorem Couret.Certificate.factorization_T_certificate

import Definitions.Def_Couret_CertificateProofs_3244eb90a0e1
import Std
import Theorems.Thm_Couret_Certificate_StepValid_sound
import Theorems.Thm_Couret_Certificate_initial_encoding
import Theorems.Thm_Couret_Certificate_observation_checked
import Theorems.Thm_Couret_Certificate_pairPresent_semantics
import Theorems.Thm_Couret_Certificate_symbol_code
import Theorems.Thm_Couret_Certificate_transitions_checked
import Theorems.Thm_Couret_decode_encode30
import Theorems.Thm_Couret_mod30_run_for_factorization
import Theorems.Thm_Couret_mul30_residue
import Theorems.Thm_Couret_residue30_injective
import Definitions.Def_Couret_CertificateData_653c7a96c17c

/-! Universal consequences of the finite certificate checks. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Couret
namespace Certificate

theorem factorization_T_certificate (w : Word Nat) (hp : w.primeFactors)
    (n : Nat) (hn : total natProduct w = n) (hc : Nat.gcd n 30 = 1) (h1 : 1 < n) :
    ∃ i : StateId,
      decoded i = State.active (encode30 n) (strictDivisorResidue n) ∧
      tableOutput i = presenceCount (entry i) ∧
      tableOutput i = outputMask (entry i) ∧
      ∀ a b : Symbol, pairPresent (entry i) a b = true ↔ arithmeticPair n a b := by sorry


































end Certificate
end Couret
