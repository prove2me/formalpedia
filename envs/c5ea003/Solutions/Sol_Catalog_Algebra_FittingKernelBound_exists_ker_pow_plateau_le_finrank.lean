-- Prove2me | solution 1 for Catalog.Algebra.FittingKernelBound.exists_ker_pow_plateau_le_finrank
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T18:45:51.182976+00:00
-- url     : https://prove2.me/submissions/77d3cbc0-e3e4-4997-ab78-64adf39d149d

-- Sol generated from Algebra/AbstractAlgebra/FittingKernelBound.lean
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Fitting kernel bound for endomorphism powers

For a finite-dimensional vector space `V` over a field `K` and an endomorphism
`g : V →ₗ[K] V`, the kernels of the powers of `g` form an *ascending* chain.  Once
two consecutive kernels coincide the chain stabilizes forever, and by counting
dimensions this plateau must occur no later than step `finrank K V`.  Hence the
kernels are constant from `finrank K V` onwards.

This is the kernel-side (dual) counterpart of the range stabilization result; the
two are proved independently here so as not to create a circular dependency.

## Main results

* `ker_pow_mono` — the chain `n ↦ ker (g ^ n)` is monotone.
* `ker_pow_succ_eq_comap` — `ker (g ^ (k+1)) = Submodule.comap g (ker (g ^ k))`.
* `ker_pow_stable` — once the kernel stabilizes at step `k` it stays constant.
* `exists_ker_pow_plateau_le_finrank` — a plateau occurs at some `k ≤ finrank K V`.
* `ker_pow_eq_of_ge_finrank` — `ker (g ^ m) = ker (g ^ finrank K V)` for `m ≥ finrank K V`.
-/


open LinearMap Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The kernel of `g ^ n` is contained in the kernel of `g ^ (n + 1)`: an ascending
chain. -/
theorem ker_pow_le_succ (g : V →ₗ[K] V) (n : ℕ) :
    ker (g ^ n) ≤ ker (g ^ (n + 1)) := by
  rw [pow_succ' g n]
  exact LinearMap.ker_le_ker_comp (g ^ n) g








theorem solution[FiniteDimensional K V] (g : V →ₗ[K] V) :
    ∃ k ≤ finrank K V, ker (g ^ (k + 1)) = ker (g ^ k) := by
  by_contra h
  push_neg at h
  -- Without a plateau, the dimension grows by at least one at each step.
  have key : ∀ k, k ≤ finrank K V + 1 → k ≤ finrank K (ker (g ^ k)) := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hjn : j ≤ finrank K V := by omega
      have hlt : ker (g ^ j) < ker (g ^ (j + 1)) :=
        lt_of_le_of_ne (ker_pow_le_succ g j) (fun e => h j hjn e.symm)
      have hstrict : finrank K (ker (g ^ j)) < finrank K (ker (g ^ (j + 1))) :=
        Submodule.finrank_lt_finrank_of_lt hlt
      have := ih (by omega)
      omega
  have h1 : finrank K V + 1 ≤ finrank K (ker (g ^ (finrank K V + 1))) := key _ le_rfl
  have h2 : finrank K (ker (g ^ (finrank K V + 1))) ≤ finrank K V := Submodule.finrank_le _
  omega
