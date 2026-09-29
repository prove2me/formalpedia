-- Prove2me | solution 1 for SymmetryBreakingCost.jacobiSym_eq_prod_sqKernel
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:01:20.744976+00:00
-- url     : https://prove2.me/submissions/78b5b144-9413-4e19-a1aa-8b0daa0f5e2c

-- Sol generated from Novelty/SymmetryBreakingCostKernel.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostFactoring
import Definitions.Def_Novelty_SymmetryBreakingCostKernel

/-!
# Exactly what the symmetric battery knows: the squarefree kernel

`Catalog/Novelty/SymmetryBreakingCostFactoring.lean` measured the *asymmetric* resource: an
oracle for `[(a i | p₀)]` isolates the hidden factor in exactly `⌈log₂ |S|⌉` queries, while the
*symmetric* battery `[(a i | N)]` computable from `N` alone prunes nothing.

This second cycle pins down the exact information content of the symmetric battery.  For a
modulus `n`, define its **squarefree kernel** `sqKernel n` to be the set of primes occurring in
`n` to an odd multiplicity.  Then:

* `jacobiSym_eq_prod_sqKernel` : for `a` coprime to `n`, `J(a | n) = ∏_{p ∈ sqKernel n} J(a | p)`.
* `jacobiSym_battery_eq_iff` : for odd `M, N > 0`, the two Jacobi batteries agree on **all**
  numerators coprime to `M * N` **iff** `sqKernel M = sqKernel N`.

So the public battery is a faithful invariant of the kernel and blind to everything else.  For a
semiprime `N = p q` the kernel is `{p, q}` — the battery reproduces `N` and not one bit more,
which is the sharp form of "zero pruning":

* `sqKernel_mul_sq` : `sqKernel (N * r ^ 2) = sqKernel N` for every `r > 0`;
* `zero_pruning_sharp` : hence for every candidate `r` there is a modulus divisible by `r` whose
  battery is *identical* to `N`'s on every admissible numerator — no candidate can be excluded.

Contrast with the asymmetric side: `exists_prescribed_signature` shows that the *individual*
Legendre symbols of the candidate primes are completely free, which is what makes `⌈log₂ |S|⌉`
oracle queries enough.  Aggregating them into a single Jacobi symbol destroys exactly that
freedom, and the destroyed freedom is the symmetry-breaking cost.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer, cycle 2): the failure of the symmetric battery is not a quantitative
weakness (few bits) but a *structural collapse*: `J(· | N)` factors through the kernel, and
distinct kernels are always separated.  If so, "zero pruning" is an exact if-and-only-if, not an
inequality.

Experiment (Experimenter): tabulated `J(a | M)` for `a = 1 … 40` and
`M ∈ {15, 135, 375, 3375, 21}` (see `ComputationalEvidence.md`).  The first four share the
kernel `{3, 5}` and produced byte-identical rows on every `a` coprime to the modulus; `21`
(kernel `{3, 7}`) differed already at `a = 2`, where `J(2 | 15) = 1` but `J(2 | 21) = -1`.

Analysis (Analyst): the separating numerator is always produced by the same mechanism as the
oracle upper bound — prescribe a nonresidue at one kernel prime and residues everywhere else,
which the Chinese remainder theorem allows.  The same CRT freedom is therefore responsible both
for the cheapness of the oracle and for the exactness of the kernel invariant.

Critique (Critic): the equivalence genuinely needs oddness of `M` and `N`: at `p = 2` there is
no quadratic nonresidue mod `2` and the argument would have to be replaced by a mod-8 argument.
The statement is therefore guarded by `Odd M`, `Odd N`, and this boundary is explicit in
`jacobiSym_battery_eq_iff`.
-/

open SymmetryBreakingCost

open Finset
open scoped NumberTheorySymbols

/-! ## 1.  Multiplicativity over a finite product -/

/-- The Jacobi symbol is multiplicative in the denominator over an arbitrary finite product. -/
theorem jacobiSym_prod_right (a : ℤ) (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ p ∈ s, f p ≠ 0) :
    J(a | ∏ p ∈ s, f p) = ∏ p ∈ s, J(a | f p) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [jacobiSym.one_right]
  | cons p T hp ih =>
      have hfT : ∀ q ∈ T, f q ≠ 0 := fun q hq => hf q (by simp [hq])
      have hprod : (∏ q ∈ T, f q) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfT
      rw [Finset.prod_cons, Finset.prod_cons,
        jacobiSym.mul_right' a (hf p (by simp)) hprod, ih hfT]

/-- Coprimality passes to divisors of the modulus. -/
theorem gcd_of_dvd {a : ℤ} {m n : ℕ} (hd : m ∣ n) (h : Int.gcd a (n : ℤ) = 1) :
    Int.gcd a (m : ℤ) = 1 := by
  have h' : Nat.Coprime a.natAbs n := by simpa [Int.gcd] using h
  simpa [Int.gcd] using Nat.Coprime.coprime_dvd_right hd h'

/-! ## 2.  The squarefree kernel -/



/-- A `±1` value raised to an exponent is itself exactly when the exponent is odd. -/
theorem pow_of_sq_eq_one {x : ℤ} (hx : x = 1 ∨ x = -1) (e : ℕ) :
    x ^ e = if Odd e then x else 1 := by
  rcases hx with rfl | rfl
  · simp
  · rcases Nat.even_or_odd e with he | he
    · simp [he.neg_one_pow, Nat.not_odd_iff_even.mpr he]
    · simp [he.neg_one_pow, he]


/-! ## 3.  Faithfulness: distinct kernels are separated -/




/-! ## 4.  Sharp zero pruning -/





open SymmetryBreakingCost in
theorem solution{a : ℤ} {n : ℕ} (hn : n ≠ 0) (hcop : Int.gcd a n = 1) :
    J(a | n) = ∏ p ∈ sqKernel n, J(a | p) := by
  classical
  have hfac : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have := Nat.factorization_prod_pow_eq_self hn
    rwa [Nat.prod_factorization_eq_prod_primeFactors] at this
  have hpm : ∀ p ∈ n.primeFactors, J(a | p) = 1 ∨ J(a | p) = -1 := by
    intro p hp
    have hpp : p ∣ n := Nat.dvd_of_mem_primeFactors hp
    have hne : J(a | p) ≠ 0 := by
      intro h0
      exact (jacobiSym.eq_zero_iff.mp h0).2 (gcd_of_dvd hpp hcop)
    rcases jacobiSym.trichotomy a p with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  calc J(a | n) = J(a | ∏ p ∈ n.primeFactors, p ^ n.factorization p) := by rw [hfac]
    _ = ∏ p ∈ n.primeFactors, J(a | p ^ n.factorization p) := by
        refine jacobiSym_prod_right a _ _ (fun p hp => ?_)
        exact pow_ne_zero _ (Nat.Prime.ne_zero (Nat.prime_of_mem_primeFactors hp))
    _ = ∏ p ∈ n.primeFactors, (if Odd (n.factorization p) then J(a | p) else 1) := by
        refine Finset.prod_congr rfl (fun p hp => ?_)
        rw [jacobiSym.pow_right, pow_of_sq_eq_one (hpm p hp)]
    _ = ∏ p ∈ sqKernel n, J(a | p) := by
        rw [sqKernel, Finset.prod_ite, Finset.prod_const_one, mul_one]
