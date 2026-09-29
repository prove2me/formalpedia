-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:29:48.634481+00:00
-- url     : https://prove2.me/theorems/60405e6b-bffa-4885-a83e-fa11fad32b3e
-- title:
--   Canonical integer states from a rational reciprocal sum
-- statement:
--   For natural a_n, integer p and natural q, defines P_n=product_(j<n) a_j, the cleared integer pP_n-q sum_(j<n)(P_n/a_j), its natural part C_n, and D_n=qP_n. Under the positive rational-reciprocal-series hypotheses, included proofs establish positive states and their exact coupled recurrences. The numerator is defined for all inputs; positivity and exact tail representation are proved with their hypotheses.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR7/CanonicalState.lean#L1-L189
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Constructing the canonical integer state and its analytic hypotheses

Compiled candidates.  The rational sum is supplied by its explicit
integer numerator p and positive natural denominator q; it is NOT replaced
by an assumed integer-tail representation.

The cleared numerator is an explicit integer finite sum.  Its positivity
is derived from the positive real tail.  All casting, exact natural
recurrences, and normalised-vanishing inputs are then concluded.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators

def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)

def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat

def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n

theorem prefixProduct_pos (a : ℕ → ℕ) (ha : ∀ n, 0 < a n) (n : ℕ) :
    0 < prefixProduct a n := by
  exact Finset.prod_pos (fun j _ ↦ ha j)

theorem prefixProduct_succ (a : ℕ → ℕ) (n : ℕ) :
    prefixProduct a (n + 1) = prefixProduct a n * a n := by
  exact Finset.prod_range_succ a n

/-- Each denominator in the prefix divides the prefix product, and the
natural quotient casts to the corresponding real quotient. -/
theorem prefix_quotient_cast (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (n j : ℕ) (hj : j ∈ Finset.range n) :
    ((prefixProduct a n / a j : ℕ) : ℝ) =
      (prefixProduct a n : ℝ) / (a j : ℝ) := by
  have hd : a j ∣ prefixProduct a n := Finset.dvd_prod_of_mem a hj
  have heq : (a j : ℝ) * ((prefixProduct a n / a j : ℕ) : ℝ) =
      (prefixProduct a n : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' hd
  have hne : (a j : ℝ) ≠ 0 := by exact_mod_cast (ha j).ne'
  apply (eq_div_iff hne).mpr
  simpa only [mul_comm] using heq

/-- Exact denominator clearing, before any positivity or limiting argument. -/
theorem clearedIntegerNumerator_cast
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q) (n : ℕ) :
    (clearedIntegerNumerator a p q n : ℝ) =
      (canonicalDenominator a q n : ℝ) *
        ((p : ℝ) / (q : ℝ) - ∑ j ∈ Finset.range n, 1 / (a j : ℝ)) := by
  have hsum : (∑ j ∈ Finset.range n,
      (q : ℝ) * ((prefixProduct a n / a j : ℕ) : ℝ)) =
      (q : ℝ) * (prefixProduct a n : ℝ) *
        (∑ j ∈ Finset.range n, 1 / (a j : ℝ)) := by
    calc
      (∑ j ∈ Finset.range n,
          (q : ℝ) * ((prefixProduct a n / a j : ℕ) : ℝ)) =
          ∑ j ∈ Finset.range n,
            ((q : ℝ) * (prefixProduct a n : ℝ)) * (1 / (a j : ℝ)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [prefix_quotient_cast a ha n j hj]
              ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hterm : ∀ j : ℕ,
      (((prefixProduct a n : ℤ) / (a j : ℤ) : ℤ) : ℝ) =
        ((prefixProduct a n / a j : ℕ) : ℝ) := by
    intro j
    norm_cast
  unfold clearedIntegerNumerator canonicalDenominator
  push_cast
  simp only [hterm]
  rw [hsum]
  field_simp [hqne]
  <;> ring

/-- The real tail is the prescribed rational sum minus its exact prefix. -/
theorem realTail_eq_rational_sub_prefix
    (a : ℕ → ℕ) (p : ℤ) (q : ℕ)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    realTail (fun k ↦ 1 / (a k : ℝ)) n =
      (p : ℝ) / (q : ℝ) - ∑ j ∈ Finset.range n, 1 / (a j : ℝ) := by
  have hsplit := hs.summable.sum_add_tsum_nat_add n
  rw [hs.tsum_eq] at hsplit
  change (∑ j ∈ Finset.range n, 1 / (a j : ℝ)) +
    realTail (fun k ↦ 1 / (a k : ℝ)) n = (p : ℝ) / (q : ℝ) at hsplit
  linarith

/-- Positive natural exact states, constructed from the rational series.
No real-limit or integer-tail assumption is hidden in the hypotheses. -/
theorem canonical_integer_tail
    (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    (∀ n, 0 < C n) ∧ (∀ n, 0 < D n) ∧
    (∀ n, C (n + 1) + D n = a n * C n) ∧
    (∀ n, D (n + 1) = a n * D n) ∧
    (∀ n, (C n : ℝ) = (D n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) n) := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  have hdpos : ∀ n, 0 < D n := by
    intro n
    exact Nat.mul_pos hq (prefixProduct_pos a ha n)
  have hreprInt : ∀ n, (clearedIntegerNumerator a p q n : ℝ) =
      (D n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) n := by
    intro n
    rw [clearedIntegerNumerator_cast a ha p q hq n,
      realTail_eq_rational_sub_prefix a p q hs n]
  have hcintpos : ∀ n, 0 < clearedIntegerNumerator a p q n := by
    intro n
    have hreal : (0 : ℝ) < (clearedIntegerNumerator a p q n : ℝ) := by
      rw [hreprInt n]
      apply mul_pos (by exact_mod_cast hdpos n)
      exact realTail_pos _ hs.summable
        (fun k ↦ one_div_pos.mpr (by exact_mod_cast ha k)) n
    exact_mod_cast hreal
  have hcast : ∀ n, (C n : ℤ) = clearedIntegerNumerator a p q n := by
    intro n
    exact Int.toNat_of_nonneg (hcintpos n).le
  have hcpos : ∀ n, 0 < C n := by
    intro n
    have hcc := hcast n
    have hp := hcintpos n
    omega
  have hrep : ∀ n, (C n : ℝ) =
      (D n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) n := by
    intro n
    have hcc : (C n : ℝ) = (clearedIntegerNumerator a p q n : ℝ) := by
      exact_mod_cast hcast n
    exact hcc.trans (hreprInt n)
  have hd : ∀ n, D (n + 1) = a n * D n := by
    intro n
    change q * prefixProduct a (n + 1) = a n * (q * prefixProduct a n)
    rw [prefixProduct_succ]
    ring
  have hc : ∀ n, C (n + 1) + D n = a n * C n := by
    intro n
    have hane : (a n : ℝ) ≠ 0 := by exact_mod_cast (ha n).ne'
    have hreal : (C (n + 1) : ℝ) + (D n : ℝ) = (a n : ℝ) * (C n : ℝ) := by
      rw [hrep (n + 1), hrep n, hd n, Nat.cast_mul,
        realTail_step _ hs.summable n]
      field_simp [hane]
      <;> ring
    exact_mod_cast hreal
  exact ⟨hcpos, hdpos, hc, hd, hrep⟩

/-- Full ordinary analytic-hypothesis bridge, as a source candidate:
rationality plus the original quadratic-growth condition produce the
canonical positive integer state, its exact dynamics, division-free
normalised vanishing, and eventual strict centring.  No parent endpoint
is concluded.  Compilation remains required. -/
theorem canonical_integer_tail_normalized
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    (∀ n, 0 < C n) ∧ (∀ n, 0 < D n) ∧
    (∀ n, C (n + 1) + D n = a n * C n) ∧
    (∀ n, D (n + 1) = a n * D n) ∧
    (∀ n, (C n : ℝ) = (D n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) n) ∧
    (∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n) ∧
    (∃ N, ∀ n, N ≤ n → Int.natAbs (E n) < C n) := by
  let C := canonicalNaturalNumerator a p q
  let D := canonicalDenominator a q
  let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
  obtain ⟨hcpos, hdpos, hc, hd, hrep⟩ := canonical_integer_tail a hapos p q hq hs
  have hnorm := normalized_vanishing_of_tail_representation a C D E ha hapos
    hcpos hdpos hc hd (fun _ ↦ rfl) hs.summable hrep hgrowth
  exact ⟨hcpos, hdpos, hc, hd, hrep, hnorm.1, hnorm.2⟩

end ErdosProblems.Erdos243.PaperCompleteR7


