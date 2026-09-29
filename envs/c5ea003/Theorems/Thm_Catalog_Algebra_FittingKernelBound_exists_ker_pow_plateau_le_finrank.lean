-- Prove2me | Theorems.Thm_Catalog_Algebra_FittingKernelBound_exists_ker_pow_plateau_le_finrank
-- name    : Catalog.Algebra.FittingKernelBound.exists_ker_pow_plateau_le_finrank
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:39:11.93881+00:00
-- url     : https://prove2.me/theorems/73b80821-09ca-4d64-832f-812e610a4005
-- title:
--   Pigeonhole: a kernel plateau occurs at some index `k ≤ finrank K V`.
-- statement:
--   Pigeonhole: a kernel plateau occurs at some index `k ≤ finrank K V`.
--
--   If no plateau occurred among the first `finrank K V` steps, each step would be a
--   strict inclusion, forcing the dimension of `ker (g ^ (finrank K V + 1))` to exceed
--   `finrank K V`, which is impossible.
--
--   ```lean
--   theorem Catalog.Algebra.FittingKernelBound.exists_ker_pow_plateau_le_finrank[FiniteDimensional K V] (g : V →ₗ[K] V) :
--       ∃ k ≤ finrank K V, ker (g ^ (k + 1)) = ker (g ^ k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/AbstractAlgebra/FittingKernelBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/AbstractAlgebra/FittingKernelBound.lean#L70

-- Thm stub generated from Algebra/AbstractAlgebra/FittingKernelBound.lean
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

theorem Catalog.Algebra.FittingKernelBound.exists_ker_pow_plateau_le_finrank[FiniteDimensional K V] (g : V →ₗ[K] V) :
    ∃ k ≤ finrank K V, ker (g ^ (k + 1)) = ker (g ^ k) := by sorry
