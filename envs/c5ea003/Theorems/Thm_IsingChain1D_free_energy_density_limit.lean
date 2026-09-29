-- Prove2me | Theorems.Thm_IsingChain1D_free_energy_density_limit
-- name    : IsingChain1D.free_energy_density_limit
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:45:34.866972+00:00
-- url     : https://prove2.me/theorems/9e512358-1d2e-4c38-9639-4f54c999b003
-- title:
--   Thermodynamic limit of the free energy density.
-- statement:
--   **Thermodynamic limit of the free energy density.** The free energy per site
--   `(1/(n+1)) · log (Zfree β J n)` converges to `log (2 cosh (β J))` as the chain
--   length tends to infinity.
--
--   ```lean
--   theorem IsingChain1D.free_energy_density_limit(β J : ℝ) :
--       Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) * Real.log (Zfree β J n))
--         Filter.atTop (nhds (Real.log (2 * Real.cosh (β * J)))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/IsingChain1D.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/IsingChain1D.lean#L139

-- Thm stub generated from Probability/IsingChain1D.lean
import Mathlib
import Definitions.Def_Probability_IsingChain1D
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The 1D Ising Model: Exact Partition Function and Absence of a Phase Transition

This file develops the **one-dimensional Ising model** with free (open) boundary
conditions completely from first principles, directly from the sum over spin
configurations, and proves three results that together make rigorous the classical
statement *"the 1D Ising model has no phase transition at any positive temperature."*

A configuration of a chain with `n` bonds (hence `n + 1` sites) is a function
`s : Fin (n+1) → Bool`, where a spin is `+1` (`true`) or `-1` (`false`) via `sp`.
The (nearest-neighbour, zero-field) Boltzmann weight of `s` is the product of the
edge factors `exp (β J σᵢ σᵢ₊₁)`, and the partition function `Zfree β J n` is the
sum of these weights over all `2 ^ (n+1)` configurations.

## Main results

* `Zfree_closed` — the **exact transfer-matrix closed form**
    `Zfree β J n = 2 * (2 * cosh (β J)) ^ n`,
  proved by a genuine induction over the chain (peel off site `0`).
* `free_energy_density_limit` — the **thermodynamic limit** of the free energy
  density exists and equals `log (2 * cosh (β J))`:
    `(1/(n+1)) * log (Zfree β J n) → log (2 * cosh (β J))`.
* `free_energy_smooth` — the free energy density `β ↦ log (2 * cosh (β J))` is
  `C^∞` on **all** of `ℝ` (in particular it is analytic and singularity-free for
  every temperature), which is exactly the statement that there is **no phase
  transition** in one dimension.

## Application keywords

statistical mechanics, Ising model, phase transition, transfer matrix,
partition function, free energy, thermodynamic limit, spin chain, probability

-- !-- Lab Notes -- !--
Hypotheses explored in this research cycle:
  (H1) The free-boundary 1D partition function has the closed form
       `Zfree = 2 (2 cosh βJ)^n`.                                    [PROVED]
  (H2) The transfer recursion `Zfree (n+1) = (2 cosh βJ) · Zfree n`
       follows by peeling site 0 via `Fin.consEquiv` and the fact
       that `∑_b exp(βJ · sp b · y) = 2 cosh(βJ)` is independent of the
       neighbouring spin `y = ±1` (uses parity of `cosh`).           [PROVED, weight_cons + sum_bool_exp]
  (H3) The free-energy density `(1/(n+1)) log Zfree` converges to
       `log(2 cosh βJ)` in the thermodynamic limit.                  [PROVED]
  (H4) The limiting free energy is `C^∞` in `β` everywhere, hence has
       NO singularity ⇒ no phase transition in 1D.                   [PROVED]
Failure analysis / dead ends:
  * Decomposing the configuration sum with `Fin.snoc` (peel the LAST site)
    forced awkward `Fin.last`/`castSucc` rewrites; peeling site `0` with
    `Fin.consEquiv` and `Fin.prod_univ_succ` is dramatically cleaner because
    the boundary edge becomes the `f 0` term of `prod_univ_succ`.
  * `simp [Finset.sum_bool]` does not exist; the Bool sum is `Fintype.sum_bool`,
    and the `if`-guards simplify with `Bool.false_eq_true`.
Insight:
  The single algebraic fact responsible for the *absence* of a 1D phase
  transition is that the transfer matrix's dominant eigenvalue `2 cosh βJ` is
  a strictly positive, real-analytic function of `β`; `log` of a positive
  analytic function is analytic, so the free energy can never be singular.
-/

open scoped BigOperators Topology
open Filter

open IsingChain1D

theorem IsingChain1D.free_energy_density_limit(β J : ℝ) :
    Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) * Real.log (Zfree β J n))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * J)))) := by sorry
