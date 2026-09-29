-- Prove2me | solution 1 for IsingChain1D.free_energy_density_limit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:49:29.121054+00:00
-- url     : https://prove2.me/submissions/3e1202aa-f4dc-4d80-8395-03364ab3c651

-- Sol generated from Probability/IsingChain1D.lean
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




/-- Summing a single boundary spin produces the transfer-matrix eigenvalue
`2 cosh (β J)`, independently of the neighbouring spin `sp b'` (which is `±1`). -/
theorem sum_bool_exp (c : ℝ) (b' : Bool) :
    (∑ b : Bool, Real.exp (c * sp b * sp b')) = 2 * Real.cosh c := by
  rw [Fintype.sum_bool, Real.cosh_eq]
  cases b' <;>
    · simp only [sp, if_true, if_false, Bool.false_eq_true, mul_one, mul_neg, neg_neg]
      ring

/-- The Boltzmann weight factorises when we prepend a spin `b` to a configuration
`t` (peeling off site `0` of the chain). -/
theorem weight_cons (β J : ℝ) (n : ℕ) (b : Bool) (t : Fin (n + 1) → Bool) :
    (∏ i : Fin (n + 1),
        Real.exp (β * J * sp ((Fin.cons b t : Fin (n + 2) → Bool) i.castSucc)
          * sp ((Fin.cons b t : Fin (n + 2) → Bool) i.succ)))
      = Real.exp (β * J * sp b * sp (t 0))
        * ∏ i : Fin n, Real.exp (β * J * sp (t i.castSucc) * sp (t i.succ)) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero]
  refine congrArg (Real.exp (β * J * sp b * sp (t 0)) * ·) ?_
  apply Finset.prod_congr rfl
  intro i _
  rw [← Fin.succ_castSucc, Fin.cons_succ]

/-- **Transfer recursion.** Adding one bond to the chain multiplies the partition
function by the dominant transfer eigenvalue `2 cosh (β J)`. -/
theorem Zfree_succ (β J : ℝ) (n : ℕ) :
    Zfree β J (n + 1) = (2 * Real.cosh (β * J)) * Zfree β J n := by
  unfold Zfree
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => Bool)), Fintype.sum_prod_type, Finset.sum_comm,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Fin.consEquiv_apply]
  simp_rw [weight_cons]
  rw [← Finset.sum_mul, sum_bool_exp]

/-- Base case: a single site (zero bonds) has `Zfree = 2` (two spin states). -/
theorem Zfree_zero (β J : ℝ) : Zfree β J 0 = 2 := by
  unfold Zfree
  simp

/-- **Exact closed form of the 1D Ising partition function** (free boundary).
For a chain of `n` bonds, `Zfree β J n = 2 (2 cosh (β J))ⁿ`. -/
theorem Zfree_closed (β J : ℝ) (n : ℕ) :
    Zfree β J n = 2 * (2 * Real.cosh (β * J)) ^ n := by
  induction n with
  | zero => simpa using Zfree_zero β J
  | succ k ih => rw [Zfree_succ, ih, pow_succ]; ring





open IsingChain1D in
theorem solution(β J : ℝ) :
    Filter.Tendsto (fun n : ℕ => (1 / (n + 1 : ℝ)) * Real.log (Zfree β J n))
      Filter.atTop (nhds (Real.log (2 * Real.cosh (β * J)))) := by
  have hc : (0:ℝ) < 2 * Real.cosh (β * J) := by have := Real.cosh_pos (x := β*J); positivity
  set L := Real.log (2 * Real.cosh (β * J)) with hL
  have hterm : ∀ n : ℕ, (1 / (n + 1 : ℝ)) * Real.log (Zfree β J n)
      = (1/(n+1:ℝ)) * Real.log 2 + (n/(n+1:ℝ)) * L := by
    intro n
    rw [Zfree_closed, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    ring
  simp_rw [hterm]
  have h1 : Tendsto (fun n : ℕ => (1/(n+1:ℝ)) * Real.log 2) atTop (nhds 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (Real.log 2)
  have h2 : Tendsto (fun n : ℕ => (n/(n+1:ℝ)) * L) atTop (nhds L) := by
    have hh : Tendsto (fun n : ℕ => (n/(n+1:ℝ))) atTop (nhds 1) := by
      simpa using tendsto_natCast_div_add_atTop (1:ℝ)
    simpa using hh.mul_const L
  simpa using h1.add h2
