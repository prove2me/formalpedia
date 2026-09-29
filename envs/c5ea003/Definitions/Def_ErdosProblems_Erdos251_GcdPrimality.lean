-- Prove2me | Definitions.Def_ErdosProblems_Erdos251_GcdPrimality
-- name    : ErdosProblems_Erdos251_GcdPrimality
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T16:41:20.861924+00:00
-- url     : https://prove2.me/theorems/5809db5c-ded5-41c5-9bef-b7c5d620e157
-- title:
--   Finite prime product and accelerated primality test
-- statement:
--   Defines the product of primes below a cutoff, the explicit product for primes below $1012$, and the accelerated primality test. The test uses a GCD in the interval $1012\le m<1013^2$ and trial division outside that interval. Correctness is established by separate theorem entries.
-- source:
--   Pinned retained Lean definitions: https://github.com/wcook04/plectis-erdos-lean/blob/d92f079c981c66a7652eb85297d506e61616c062/ErdosProblems/Erdos251/GcdPrimality.lean#L34-L36; https://github.com/wcook04/plectis-erdos-lean/blob/d92f079c981c66a7652eb85297d506e61616c062/ErdosProblems/Erdos251/GcdPrimality.lean#L101-L102; https://github.com/wcook04/plectis-erdos-lean/blob/d92f079c981c66a7652eb85297d506e61616c062/ErdosProblems/Erdos251/GcdPrimality.lean#L111-L114

import Definitions.Def_ErdosProblems_Erdos251_PrimeGapDyadicTail
import Definitions.Def_ErdosProblems_Erdos251_KernelDenominatorFloor
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Periodic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PowModTotient
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Primality by one gcd below `1013 ^ 2`

The large certificate for Erdős Problem #251 scans every integer below
`1023068` and decides which of them are prime (`PaperStreamingCertificateV5`).
With trial division that scan needs hours of kernel time. This module gives a
primality test that the kernel evaluates with one gcd per integer on the
scanned range, and proves that it agrees with trial division everywhere.

The criterion is `prime_iff_gcd`: for `1012 ≤ m < 1013 ^ 2`, the integer `m`
is prime exactly when `gcd m P = 1`, where `P` is the product of the primes
below `1012`. Every prime factor of `P` is below `1012`, so a prime `m ≥ 1012`
does not divide `P` and is coprime to it. A composite `m` in the range has a
prime factor `q` with `q ^ 2 ≤ m < 1013 ^ 2`. Then `q ≤ 1012`, and `q < 1012`
because `1012` is not prime, so `q` divides both `m` and `P`.

`P` is written as the literal `P1011`. The kernel recomputes the product from
the trial-division test `isPrimeTD` and checks that it equals the literal
(`primeProd_1012`), so no supplied list of primes is trusted. The test
`isPrimeG` uses the gcd on `[1012, 1013 ^ 2)` and trial division elsewhere,
and `isPrimeG_eq` proves `isPrimeG m = isPrimeTD m` for every natural number
`m`. Replacing one test by the other in the certificate changes the cost of
the check and leaves every statement unchanged.
-/

namespace ErdosProblems.Erdos251.PaperV5.Fast

open ErdosProblems.Erdos251

/-- The product of the primes below `n`, with primality decided by trial
division. -/
def primeProd : ℕ → ℕ
  | 0 => 1
  | n + 1 => if isPrimeTD n then n * primeProd n else primeProd n







/-- The product of the 169 primes below `1012`, a literal of 1390 bits. -/
def P1011 : ℕ :=
  19766653710804075182143870771990238475539088142104672537897548776929384313227289497808619213628587662490595625147474943321532235492742204128846913537770322864572995974935654100594289056885746177674106727111011492167293600757722582873710083333409221248630824126186603003458015947013676475012954103807759699698139884769988141115940629691053820740641161140263635520790129447288872867072881843138566340347306438762146043190



/-- Primality with one gcd on `[1012, 1013 ^ 2)` and trial division
elsewhere. -/
def isPrimeG (m : ℕ) : Bool :=
  bif Nat.blt m 1012 then isPrimeTD m
  else bif Nat.blt m 1026169 then Nat.beq (Nat.gcd m P1011) 1
  else isPrimeTD m









end ErdosProblems.Erdos251.PaperV5.Fast


