-- Prove2me | solution 1 for RelWalkCount.rowSum_pow
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:39:01.97159+00:00
-- url     : https://prove2.me/submissions/4d1da4db-53fe-4b86-86f9-90b79682e18c

-- Sol generated from Algebra/NonBacktracking/RelWalkCount.lean
import Mathlib
import Definitions.Def_Algebra_NonBacktracking_RelWalkCount

/-!
# Counting walks in a digraph by powers of its 0-1 matrix

This file develops, from scratch, the combinatorial interpretation of the entries and
the trace of powers of the incidence (0-1) matrix of an *arbitrary* decidable relation
`r : ι → ι → Prop` on a finite type `ι`.

Mathlib provides such a statement only for the adjacency matrix of a `SimpleGraph`
(`SimpleGraph.adjMatrix_pow_apply_eq_card_walk`).  The relation we ultimately care
about — "arc `f` follows arc `e` without backtracking" — is **not symmetric**, so the
`SimpleGraph` machinery does not apply and the theory has to be redone for a general
directed relation.

## Main definitions

* `RelWalkCount.relMatrix r` — the 0-1 matrix of `r` over `ℕ`.
* `RelWalkCount.walks r n a b` — the finset of walks of length `n` (i.e. lists of
  `n + 1` vertices) from `a` to `b` all of whose consecutive pairs are `r`-related.
* `RelWalkCount.closedWalks r n` — the finset of *rooted closed* walks of length `n`:
  walks of length `n` whose first and last entry agree.

## Main results

* `RelWalkCount.mem_walks` — the recursive definition of `walks` really describes the
  set of `r`-chains of the prescribed length and endpoints.
* `RelWalkCount.relMatrix_pow_apply` — `(M ^ n) a b` is the number of walks from `a`
  to `b` of length `n`.
* `RelWalkCount.trace_relMatrix_pow` — `trace (M ^ n)` is the number of rooted closed
  walks of length `n`.
* `RelWalkCount.rowSum_pow` — if every row of `M` sums to `q`, then every row of
  `M ^ n` sums to `q ^ n`; consequently `trace (M ^ n) ≤ card ι * q ^ n`.
-/

open Finset Matrix

open RelWalkCount


variable {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ι → ι → Prop) [DecidableRel r]













/-! ### Row sums -/




open RelWalkCount in
theorem solution{q : ℕ} (hq : ∀ a : ι, ∑ b, relMatrix r a b = q) :
    ∀ (n : ℕ) (a : ι), ∑ b, (relMatrix r ^ n) a b = q ^ n := by
  intro n
  induction n with
  | zero => intro a; simp [Matrix.one_apply, Finset.sum_ite_eq]
  | succ n ih =>
      intro a
      have hpow : ∀ b, (relMatrix r ^ (n + 1)) a b
          = ∑ c, relMatrix r a c * (relMatrix r ^ n) c b := by
        intro b; rw [pow_succ', Matrix.mul_apply]
      simp only [hpow]
      rw [Finset.sum_comm]
      have hsum : ∀ c ∈ (univ : Finset ι),
          ∑ b, relMatrix r a c * (relMatrix r ^ n) c b = relMatrix r a c * q ^ n := by
        intro c _
        rw [← Finset.mul_sum, ih c]
      rw [Finset.sum_congr rfl hsum, ← Finset.sum_mul, hq a, pow_succ]
      ring
