-- Prove2me | solution 1 for Round10.freeWitness_prod_coprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:49:13.070373+00:00
-- url     : https://prove2.me/submissions/5e8b958d-c589-425f-b191-ee63ce1a3443

-- Sol generated from Geometry/Round10Closures/CarmichaelThreshold.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
import Theorems.Thm_Round10_freeWitness_mul
import Theorems.Thm_Round10_freeWitness_one
/-
Round-10 Closures — Part IX (cycle 5): the aggregation depth of an arbitrary odd modulus.

Cycle 4 identified the exact aggregation depth of the free-witness channel for semiprimes
and for squarefree moduli: the least exponent with a maximal witness is `lcm_{r ∣ N}(r-1)`.
Cycle 5 removes the squarefree hypothesis on the odd part: for *every* odd `N`,

    R_k(N) = ∏_{p ∣ N} gcd(φ(p^{v_p(N)}), k),

and the least positive exponent with `R_k(N) = φ(N)` is the Carmichael exponent
`λ(N) = lcm_{p ∣ N} φ(p^{v_p(N)})`.

The only input beyond the previous cycles is the cyclicity of `(ZMod (p^e))ˣ` for odd
primes; the `2`-adic case is genuinely different (the local group is not cyclic for
`8 ∣ N`) and is left open.
-/

open Round10









open Round10 in
theorem solution(k : ℕ) :
    ∀ (P : Finset ℕ) (f : ℕ → ℕ), (∀ a ∈ P, ∀ b ∈ P, a ≠ b → Nat.Coprime (f a) (f b)) →
      freeWitness (∏ i ∈ P, f i) k = ∏ i ∈ P, freeWitness (f i) k := by
  classical
  intro P
  induction P using Finset.induction with
  | empty => intro f _; simpa using freeWitness_one k
  | insert a P ha ih =>
      intro f hcop
      have hcop' : Nat.Coprime (f a) (∏ i ∈ P, f i) :=
        Nat.Coprime.prod_right fun i hi =>
          hcop a (Finset.mem_insert_self a P) i (Finset.mem_insert_of_mem hi)
            (by rintro rfl; exact ha hi)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, freeWitness_mul hcop',
        ih f fun x hx y hy hxy =>
          hcop x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy]
