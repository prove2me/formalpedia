-- Prove2me | solution 1 for ResidueDial.two_mul_prefixCost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:50:38.963664+00:00
-- url     : https://prove2.me/submissions/aa1ef1e1-8923-4760-b499-279858ba409a

-- Sol generated from Cryptography/ResidueDial/MultiSymbol.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Core
import Definitions.Def_Cryptography_ResidueDial_MultiSymbol

/-!
# Multi-symbol dials: the hierarchy of caps `2r/(r+1)`

A binary dial splits the class space into two blocks (kept / rejected) and is
capped at `4/3`.  An `r`-symbol dial splits it into `r` blocks, scanned in some
order; the scan pays, for a target in the `i`-th block, everything up to and
including that block.  Its normalised cost is

  `prefixCost θ = Σ_i θ_i (θ_1 + … + θ_i)`.

Three facts are proved here.

* `two_mul_prefixCost` — the **order-free identity**
  `2 · prefixCost θ = (Σ θ)² + Σ θ²`.  In particular the cost does not depend on
  the order in which the blocks are scanned (`prefixCost_comp_perm`): there is
  no clever ordering to find, contrary to what one might expect from a
  rearrangement heuristic.
* `multiSpeedup_le_cap` — the **cap hierarchy**: for a dial with `r` blocks,
  `Speedup ≤ 2r/(r+1)`, attained exactly at uniform blocks
  (`multiSpeedup_uniform`).  At `r = 2` this is the `4/3` of `Core.lean`
  (`prefixCost_two_eq_dialCost`, `cap_two_eq_four_thirds`).
* `cap_lt_two`, `cap_tendsto_two` — the hierarchy is strictly below `2` and
  converges to it: the asked barrier `2` is the `r → ∞` limit of the
  multi-symbol caps, never a value.
-/

open ResidueDial

open Finset












/-! ## Boundary: what would break the cap

The cap `2r/(r+1)` — and with it the `4/3` of `Core.lean` — is a statement about
*single-pass scans*: the dial reorders the blocks, but a block once scheduled is
paid for.  If instead the dial's answer lets the algorithm **skip** the blocks it
has ruled out, the cost is `Σ θ²` and the cap disappears: a balanced `r`-symbol
full reveal buys exactly `r`.  This is the precise boundary of the converse, and
it is where the barrier-`2` framing of the binary case comes from
(`revealSpeedup_binary_half`). -/







open ResidueDial in
theorem solution{r : ℕ} (θ : Fin r → ℝ) :
    2 * prefixCost θ = (∑ i, θ i) ^ 2 + ∑ i, (θ i) ^ 2 := by
  classical
  have hP : prefixCost θ = ∑ i, ∑ j, (if j ≤ i then θ i * θ j else 0) := by
    unfold prefixCost
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_filter]
  have hQ : ∑ i, ∑ j, (if i ≤ j then θ i * θ j else 0) = prefixCost θ := by
    rw [Finset.sum_comm, hP]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j ≤ i <;> simp [h, mul_comm]
  have hpoint : ∀ i j : Fin r,
      (if j ≤ i then θ i * θ j else 0) + (if i ≤ j then θ i * θ j else 0)
        = θ i * θ j + (if i = j then θ i * θ j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [not_le.mpr h, le_of_lt h, ne_of_lt h]
    · subst h; simp
    · simp [not_le.mpr h, le_of_lt h, ne_of_gt h]
  have hsum : 2 * prefixCost θ
      = ∑ i, ∑ j, (θ i * θ j + (if i = j then θ i * θ j else 0)) := by
    rw [two_mul]
    nth_rewrite 1 [hP]
    nth_rewrite 1 [← hQ]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by linarith [hpoint i j]
  rw [hsum]
  have hinner : ∀ i : Fin r, ∑ j, (θ i * θ j + if i = j then θ i * θ j else 0)
      = θ i * (∑ j, θ j) + θ i ^ 2 := by
    intro i
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_ite_eq (univ : Finset (Fin r)) i (fun j => θ i * θ j)]
    simp [sq]
  rw [Finset.sum_congr rfl (fun i _ => hinner i), Finset.sum_add_distrib, ← Finset.sum_mul]
  ring
