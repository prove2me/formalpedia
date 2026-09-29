-- Prove2me | solution 1 for SymmetryBreakingCost.jacobiSym_battery_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:07:13.095165+00:00
-- url     : https://prove2.me/submissions/cbeb37e1-156f-4301-86b4-a84a1e5021fa

-- Sol generated from Novelty/SymmetryBreakingCostKernel.lean
import Mathlib
import Definitions.Def_Novelty_SymmetryBreakingCostFactoring
import Definitions.Def_Novelty_SymmetryBreakingCostKernel
import Theorems.Thm_SymmetryBreakingCost_exists_separating_numerator
import Theorems.Thm_SymmetryBreakingCost_jacobiSym_eq_prod_sqKernel

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


/-- Coprimality passes to divisors of the modulus. -/
theorem gcd_of_dvd {a : ℤ} {m n : ℕ} (hd : m ∣ n) (h : Int.gcd a (n : ℤ) = 1) :
    Int.gcd a (m : ℤ) = 1 := by
  have h' : Nat.Coprime a.natAbs n := by simpa [Int.gcd] using h
  simpa [Int.gcd] using Nat.Coprime.coprime_dvd_right hd h'

/-! ## 2.  The squarefree kernel -/





/-! ## 3.  Faithfulness: distinct kernels are separated -/




/-! ## 4.  Sharp zero pruning -/





open SymmetryBreakingCost in
theorem solution{M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0) (hMo : Odd M) (hNo : Odd N) :
    (∀ a : ℤ, Int.gcd a (M * N) = 1 → J(a | M) = J(a | N)) ↔ sqKernel M = sqKernel N := by
  classical
  constructor
  · intro hbat
    by_contra hne
    obtain ⟨p, hp⟩ : ∃ p, ¬(p ∈ sqKernel M ↔ p ∈ sqKernel N) := by
      by_contra hc
      push_neg at hc
      exact hne (Finset.ext hc)
    rcases Classical.em (p ∈ sqKernel M) with hpM | hpM
    · have hpN : p ∉ sqKernel N := fun h => hp ⟨fun _ => h, fun _ => hpM⟩
      obtain ⟨a, hcop, h1, h2⟩ := exists_separating_numerator hM hN hMo hNo hpM hpN
      have := hbat a hcop
      rw [h1, h2] at this
      norm_num at this
    · have hpN : p ∈ sqKernel N := by
        by_contra h
        exact hp ⟨fun hx => absurd hx hpM, fun hx => absurd hx h⟩
      obtain ⟨a, hcop, h1, h2⟩ :=
        exists_separating_numerator hN hM hNo hMo hpN hpM
      have := hbat a (by rw [mul_comm]; exact hcop)
      rw [h1, h2] at this
      norm_num at this
  · intro hker a hcop
    have hcopM : Int.gcd a M = 1 := gcd_of_dvd (dvd_mul_right M N) (by exact_mod_cast hcop)
    have hcopN : Int.gcd a N = 1 := gcd_of_dvd (dvd_mul_left N M) (by exact_mod_cast hcop)
    rw [jacobiSym_eq_prod_sqKernel hM hcopM, jacobiSym_eq_prod_sqKernel hN hcopN, hker]
