-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:29:13.273944+00:00
-- url     : https://prove2.me/theorems/d275b100-c76c-4b29-9378-b3f3c510b0a6
-- title:
--   Real reciprocal tails and analytic bridges
-- statement:
--   For a real sequence t, defines its tail at n as the infinite sum of t_(k+n) over k≥0. Included source proofs establish tail decomposition under summability, positivity under positive terms, geometric comparison, and the leading-term asymptotic when successive ratios tend to zero. The reciprocal-growth bridge carries its stated analytic hypotheses.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR7/RealTail.lean#L1-L250
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR7.RealTail.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
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
# Analytic part of the canonical tail bridge

Compiled candidates.  The principal analytic assertion is proved, not
postulated: if positive summable terms have successive ratio tending to
zero, their tail divided by the leading term tends to one.

The final theorem derives normalised vanishing from quadratic growth and
an exact tail representation.  It does NOT claim to have constructed the
canonical integer state, proved its integrality, or obtained the sharper
O(1/a_n) expansion required elsewhere in the papers.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR7

open Filter
open scoped BigOperators

noncomputable def realTail (t : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, t (k + n)

theorem realTail_step (t : ℕ → ℝ) (ht : Summable t) (n : ℕ) :
    realTail t n = t n + realTail t (n + 1) := by
  have hs : Summable (fun k : ℕ ↦ t (k + n)) := (summable_nat_add_iff n).mpr ht
  simpa only [realTail, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm,
    Nat.add_comm] using hs.tsum_eq_zero_add

theorem realTail_nonneg (t : ℕ → ℝ) (hpos : ∀ n, 0 ≤ t n) (n : ℕ) :
    0 ≤ realTail t n := by
  exact tsum_nonneg (fun k ↦ hpos (k + n))

theorem realTail_leading_term (t : ℕ → ℝ) (ht : Summable t)
    (hpos : ∀ n, 0 ≤ t n) (n : ℕ) : t n ≤ realTail t n := by
  rw [realTail_step t ht n]
  have hp := realTail_nonneg t hpos (n + 1)
  linarith

theorem realTail_pos (t : ℕ → ℝ) (ht : Summable t)
    (hpos : ∀ n, 0 < t n) (n : ℕ) : 0 < realTail t n :=
  (hpos n).trans_le (realTail_leading_term t ht (fun k ↦ (hpos k).le) n)

/-- A uniform one-step ratio bound on a tail gives the full geometric
majorant.  Both infinite sums in the comparison have summability proofs. -/
theorem realTail_geometric_bound
    (t : ℕ → ℝ) (ht : Summable t) (hpos : ∀ n, 0 ≤ t n)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1) (N n : ℕ) (hn : N ≤ n)
    (hstep : ∀ j, N ≤ j → t (j + 1) ≤ r * t j) :
    realTail t n ≤ (1 - r)⁻¹ * t n := by
  have hmajor : ∀ k : ℕ, t (k + n) ≤ r ^ k * t n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          t (k + 1 + n) = t ((k + n) + 1) := by congr 1 <;> omega
          _ ≤ r * t (k + n) := hstep (k + n) (by omega)
          _ ≤ r * (r ^ k * t n) := mul_le_mul_of_nonneg_left ih hr
          _ = r ^ (k + 1) * t n := by rw [pow_succ]; ring
  have hg : HasSum (fun k : ℕ ↦ r ^ k) ((1 - r)⁻¹) :=
    hasSum_geometric_of_abs_lt_one (by rwa [abs_of_nonneg hr])
  have hgm : HasSum (fun k : ℕ ↦ r ^ k * t n) ((1 - r)⁻¹ * t n) :=
    hg.mul_right (t n)
  have hs : Summable (fun k : ℕ ↦ t (k + n)) := (summable_nat_add_iff n).mpr ht
  calc
    realTail t n ≤ ∑' k : ℕ, r ^ k * t n :=
      hs.tsum_le_tsum hmajor hgm.summable
    _ = (1 - r)⁻¹ * t n := hgm.tsum_eq

/-- Positive terms with successive ratio tending to zero have tails
asymptotic to their leading term.  This is a complete analytic lemma,
not a bound supplied as a hypothesis to a formal endpoint. -/
theorem realTail_div_term_tendsto_one
    (t : ℕ → ℝ) (ht : Summable t) (hpos : ∀ n, 0 < t n)
    (hratio : Tendsto (fun n ↦ t (n + 1) / t n) atTop (nhds 0)) :
    Tendsto (fun n ↦ realTail t n / t n) atTop (nhds 1) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let r : ℝ := min (ε / 4) (1 / 4)
  have hrpos : 0 < r := lt_min (by positivity) (by norm_num)
  have hrquarter : r ≤ 1 / 4 := min_le_right _ _
  have hreps : r ≤ ε / 4 := min_le_left _ _
  have hr1 : r < 1 := by linarith
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hratio r hrpos
  have hstep : ∀ j, N ≤ j → t (j + 1) ≤ r * t j := by
    intro j hj
    have hnonneg : 0 ≤ t (j + 1) / t j := div_nonneg (hpos _).le (hpos _).le
    have hh : t (j + 1) / t j < r := by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hN j hj
    exact (div_le_iff₀ (hpos j)).mp hh.le
  refine ⟨N, fun n hn ↦ ?_⟩
  have hlow : 1 ≤ realTail t n / t n := by
    apply (le_div_iff₀ (hpos n)).mpr
    simpa only [one_mul] using
      realTail_leading_term t ht (fun k ↦ (hpos k).le) n
  have hhigh : realTail t n / t n ≤ (1 - r)⁻¹ := by
    apply (div_le_iff₀ (hpos n)).mpr
    exact realTail_geometric_bound t ht (fun k ↦ (hpos k).le)
      r hrpos.le hr1 N n hn hstep
  have hden : 0 < 1 - r := by linarith
  have hinv : (1 - r)⁻¹ ≤ 1 + 2 * r := by
    rw [← one_div]
    apply (div_le_iff₀ hden).mpr
    have hp : 0 ≤ r * (1 - 2 * r) := mul_nonneg hrpos.le (by linarith)
    nlinarith
  have habs : |realTail t n / t n - 1| < ε := by
    rw [abs_of_nonneg (by linarith : 0 ≤ realTail t n / t n - 1)]
    linarith
  simpa only [Real.dist_eq] using habs

theorem shift_tendsto_atTop (k : ℕ) :
    Tendsto (fun n : ℕ ↦ n + k) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro B
  exact ⟨B, fun n hn ↦ by omega⟩

/-- Strict increase and positivity give the real divergence needed for
reciprocals; it is not inserted as an additional growth assumption. -/
theorem strictMono_nat_cast_tendsto_atTop
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n) :
    Tendsto (fun n ↦ (a n : ℝ)) atTop atTop := by
  have hlarge : ∀ n, n < a n := by
    intro n
    induction n with
    | zero => exact hpos 0
    | succ n ih =>
        have hs : a n < a (n + 1) := ha (Nat.lt_succ_self n)
        omega
  have hnat : Tendsto a atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro B
    exact ⟨B, fun n hn ↦ hn.trans (hlarge n).le⟩
  exact tendsto_natCast_atTop_atTop.comp hnat

/-- Quadratic denominator growth implies successive reciprocal terms
have ratio zero.  The hypothesis uses the paper's a_(n+1)/a_n^2 ratio. -/
theorem reciprocal_successive_ratio_tendsto_zero
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    Tendsto (fun n ↦ (1 / (a (n + 1) : ℝ)) / (1 / (a n : ℝ)))
      atTop (nhds 0) := by
  have hinv : Tendsto (fun n ↦ (a n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (strictMono_nat_cast_tendsto_atTop a ha hpos)
  have hq : Tendsto (fun n ↦ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))
      atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using hgrowth.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hm := hq.mul hinv
  have hlim : Tendsto
      (fun n ↦ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) * (a n : ℝ)⁻¹)
      atTop (nhds 0) := by simpa only [one_mul] using hm
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
    field_simp [h0, h1]
    <;> ring

/-- The scaled consecutive real-tail ratio tends to one under the
actual growth condition, using only summability of the reciprocal series. -/
theorem scaled_reciprocal_tail_ratio_tendsto_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hsum : Summable (fun n ↦ 1 / (a n : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    Tendsto (fun n ↦ (a n : ℝ) * realTail (fun k ↦ 1 / (a k : ℝ)) (n + 1) /
      realTail (fun k ↦ 1 / (a k : ℝ)) n) atTop (nhds 1) := by
  let t : ℕ → ℝ := fun n ↦ 1 / (a n : ℝ)
  have htpos : ∀ n, 0 < t n := fun n ↦ by
    dsimp [t]
    exact one_div_pos.mpr (by exact_mod_cast hpos n)
  have hratio := reciprocal_successive_ratio_tendsto_zero a ha hpos hgrowth
  have hrel : Tendsto (fun n ↦ realTail t n / t n) atTop (nhds 1) :=
    realTail_div_term_tendsto_one t hsum htpos hratio
  have hq : Tendsto (fun n ↦ (a n : ℝ) ^ 2 / (a (n + 1) : ℝ))
      atTop (nhds 1) := by
    simpa only [inv_div, inv_one] using hgrowth.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hrnext := hrel.comp (shift_tendsto_atTop 1)
  have hlim := (hq.mul hrnext).div hrel (by norm_num : (1 : ℝ) ≠ 0)
  have hlim' : Tendsto (fun n ↦
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ)) * (realTail t (n + 1) / t (n + 1)) /
        (realTail t n / t n)) atTop (nhds 1) := by
    simpa only [one_mul, div_one, Function.comp_apply] using hlim
  apply hlim'.congr'
  exact Filter.Eventually.of_forall fun n ↦ by
    have h0 : (a n : ℝ) ≠ 0 := by exact_mod_cast (hpos n).ne'
    have h1 : (a (n + 1) : ℝ) ≠ 0 := by exact_mod_cast (hpos (n + 1)).ne'
    have hx : realTail t n ≠ 0 := (realTail_pos t hsum htpos n).ne'
    dsimp only [t]
    field_simp [h0, h1, hx]
    <;> ring

/-- Analytic-to-arithmetic bridge with an explicit real-tail
representation.  This finishes the normalised-vanishing implication once
the canonical integer state has been constructed; that construction is
not smuggled into the conclusion. -/
theorem normalized_vanishing_of_tail_representation
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hsum : Summable (fun n ↦ 1 / (a n : ℝ)))
    (hrep : ∀ n, (C n : ℝ) = (D n : ℝ) *
      realTail (fun k ↦ 1 / (a k : ℝ)) n)
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    (∀ K : ℕ, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n) ∧
    (∃ N, ∀ n, N ≤ n → Int.natAbs (E n) < C n) := by
  have hr := scaled_reciprocal_tail_ratio_tendsto_one a ha hapos hsum hgrowth
  have hquot : Tendsto (fun n ↦ (C (n + 1) : ℝ) / (C n : ℝ))
      atTop (nhds 1) := by
    apply hr.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      dsimp only
      rw [hrep (n + 1), hrep n, hD n, Nat.cast_mul]
      have hd0 : (D n : ℝ) ≠ 0 := by exact_mod_cast (hDpos n).ne'
      have hx : realTail (fun k ↦ 1 / (a k : ℝ)) n ≠ 0 := by
        exact (realTail_pos _ hsum (fun k ↦ one_div_pos.mpr
          (by exact_mod_cast hapos k)) n).ne'
      field_simp [hd0, hx]
      <;> ring
  have herr : Tendsto (fun n ↦ (E n : ℝ) / (C n : ℝ)) atTop (nhds 0) := by
    have hz := (tendsto_const_nhds (x := (1 : ℝ))).sub hquot
    have hz' : Tendsto (fun n ↦ 1 - (C (n + 1) : ℝ) / (C n : ℝ))
        atTop (nhds 0) := by simpa only [sub_self] using hz
    apply hz'.congr'
    exact Filter.Eventually.of_forall fun n ↦ by
      dsimp only
      have hs : (C (n + 1) : ℝ) = (C n : ℝ) - (E n : ℝ) := by
        exact_mod_cast natTail_eq_sub_centeredState a C D E hC hE n
      have hc0 : (C n : ℝ) ≠ 0 := by exact_mod_cast (hCpos n).ne'
      rw [hs]
      field_simp [hc0]
      <;> ring
  have habs : Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0) := by
    have hx : Tendsto (fun n ↦ |(E n : ℝ) / (C n : ℝ)|) atTop (nhds 0) := by
      simpa only [abs_zero] using herr.abs
    refine hx.congr fun n ↦ ?_
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (C n : ℝ))]
  have hv := (normalized_vanishing_iff C E hCpos).mp habs
  refine ⟨hv, ?_⟩
  obtain ⟨N, hN⟩ := hv 1
  exact ⟨N, fun n hn ↦ by simpa only [one_mul] using hN n hn⟩

end ErdosProblems.Erdos243.PaperCompleteR7


