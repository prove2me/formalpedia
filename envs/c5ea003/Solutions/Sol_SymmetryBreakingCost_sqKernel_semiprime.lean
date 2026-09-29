-- Prove2me | solution 1 for SymmetryBreakingCost.sqKernel_semiprime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:07:14.0619+00:00
-- url     : https://prove2.me/submissions/28f1ff64-651d-4225-9b02-a1912f77f12c

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



/-! ## 2.  The squarefree kernel -/


theorem mem_sqKernel_iff {n p : ℕ} : p ∈ sqKernel n ↔ Odd (n.factorization p) := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    have hne : n.factorization p ≠ 0 := by
      rcases h with ⟨m, hm⟩; omega
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr hne



/-! ## 3.  Faithfulness: distinct kernels are separated -/




/-! ## 4.  Sharp zero pruning -/





open SymmetryBreakingCost in
theorem solution{p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    sqKernel (p * q) = {p, q} := by
  classical
  ext r
  rw [mem_sqKernel_iff, Nat.factorization_mul hp.ne_zero hq.ne_zero]
  simp only [Finsupp.coe_add, Pi.add_apply, hp.factorization, hq.factorization,
    Finsupp.single_apply, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    rw [if_neg (fun hh => hc.1 hh.symm), if_neg (fun hh => hc.2 hh.symm)] at h
    simp at h
  · rintro (rfl | rfl)
    · rw [if_pos rfl, if_neg (fun hh => hpq hh.symm)]
      exact ⟨0, by omega⟩
    · rw [if_neg (fun hh => hpq hh), if_pos rfl]
      exact ⟨0, by omega⟩
