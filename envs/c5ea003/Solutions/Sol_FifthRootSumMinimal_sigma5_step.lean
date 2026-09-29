-- Prove2me | solution 1 for FifthRootSumMinimal.sigma5_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:54:16.461865+00:00
-- url     : https://prove2.me/submissions/c4dc7fb0-b1d3-4e11-88c3-d86b3ab245e1

-- Sol generated from Novelty/FifthRootSumMonotonicity.lean
import Mathlib
import Definitions.Def_Novelty_FifthRootSumMinimal
import Theorems.Thm_FifthRootSumMinimal_sigma5_bddBelow
import Theorems.Thm_FifthRootSumMinimal_sigma5_set_nonempty
import Theorems.Thm_FifthRootSumMinimal_zeta5_geom_sum

/-!
# Monotonicity of `σ₅` along residue classes modulo 5

Using the definition of `σ₅` (`FifthRootSumMinimal.sigma5`) — the minimal absolute value
of a sum of `n` powers of the primitive fifth root of unity `ζ₅` — we prove the
conjecture that for each residue `r ∈ {0,1,2,3,4}` the sequence

  `k ↦ σ₅ (5 k + r)`

is non-increasing.

## The idea

The five roots satisfy `∑_{i < 5} ζ₅ ^ i = 0` (`FifthRootSumMinimal.zeta5_geom_sum`).
Hence, given any sum `S = ∑_{j < n} ζ₅ ^ (c j)` of `n` powers, we may append the five
exponents `0,1,2,3,4` to obtain a sum of `n + 5` powers with *the same value* `S`.
Therefore every absolute value attainable with `n` powers is also attainable with
`n + 5` powers, i.e. `sumAbsSet n ⊆ sumAbsSet (n + 5)`, and taking infima gives the
one-step inequality `σ₅ (n + 5) ≤ σ₅ n` (`sigma5_step`).

Specialising `n = 5 k + r` and noting `5 (k + 1) + r = (5 k + r) + 5` yields the
residue-wise monotonicity.

## No circular reasoning

`σ₅` is defined once and for all in `FifthRootSumMinimal`; the argument here only uses
the geometric-sum identity for `ζ₅` and elementary properties of infima of sets of
reals, so it is free of self-reference.  Exponent bookkeeping modulo `5` is governed by
the multiplicative order-`5` reduction `zeta5_pow_mod`, the fifth-root analogue of the
Fermat-little-theorem congruence recorded in
`Catalog.FINAL.Probability.FermatLittleFive`.
-/

open scoped BigOperators

open FifthRootSumMinimal






theorem solution(n : ℕ) : sigma5 (n + 5) ≤ sigma5 n := by
  apply csInf_le_csInf (sigma5_bddBelow (n + 5)) (sigma5_set_nonempty n)
  rintro x ⟨c, rfl⟩
  refine ⟨fun i => if i < n then c i else i - n, ?_⟩
  simp only
  rw [Finset.sum_range_add]
  have h1 : ∑ i ∈ Finset.range n, zeta5 ^ (if i < n then c i else i - n)
          = ∑ i ∈ Finset.range n, zeta5 ^ c i := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    simp [hi]
  have h2 : ∑ i ∈ Finset.range 5, zeta5 ^ (if n + i < n then c (n + i) else (n + i) - n)
          = 0 := by
    have hcongr : ∀ i ∈ Finset.range 5,
        zeta5 ^ (if n + i < n then c (n + i) else (n + i) - n) = zeta5 ^ i := by
      intro i _
      have hlt : ¬ (n + i < n) := by omega
      simp [hlt]
    rw [Finset.sum_congr rfl hcongr, zeta5_geom_sum]
  rw [h1, h2, add_zero]
