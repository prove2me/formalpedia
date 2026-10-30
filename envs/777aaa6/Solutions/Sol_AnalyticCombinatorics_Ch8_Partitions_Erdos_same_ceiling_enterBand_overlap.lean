-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.same_ceiling_enterBand_overlap
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T18:41:43.320261+00:00
-- url     : https://prove2.me/submissions/5c386328-3dfa-45f4-a4f2-45228345c1d1

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankBandEntrance
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_SigmaRecurrence
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_UpperBound
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ErdosKernel
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KernelBarriers
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_PartitionRenewal
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_RankBandEntrance_x1
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_erdosWeight_nonneg_of_lt
import Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_kernelMass_sub_one_rate
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
namespace AnalyticCombinatorics.Ch8.Partitions.Sigma

open scoped BigOperators

lemma sigmaR_eq_sum_divisors (m : ℕ) :
    sigmaR m = ∑ d ∈ m.divisors, (d : ℝ) := by
  rw [sigmaR, ArithmeticFunction.sigma_one_apply]
  norm_num

end AnalyticCombinatorics.Ch8.Partitions.Sigma
end

section
namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

open Filter
open scoped BigOperators Topology

noncomputable section

lemma C_pos : 0 < C := by
  dsimp [C]
  positivity

lemma sigmaR_nonneg (n : ℕ) : 0 ≤ Sigma.sigmaR n := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  exact Finset.sum_nonneg fun d _hd => by positivity

lemma erdosWeight_nonneg_of_mem {n m : ℕ} (hm : m ∈ Finset.Icc 1 (n - 1)) :
    0 ≤ erdosWeight n m := by
  have hmI := Finset.mem_Icc.mp hm
  exact erdosWeight_nonneg_of_lt (n := n) (m := m) (by omega)

end
end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

section
/-!
# R7 Layer 1: instantiation of the renewal spine to the partition kernel

Defines the predecessor transition kernel `Pker n k = erdosWeight n (n−k)/kernelMass n`, the rank
`rnk n = ⌊3√n⌋` (`ρ=3` makes window steps strictly drop rank), and the residual `dres`.  Proves the
kernel facts that feed the banked spine (`rec_iter_bound`, `pot_le_block_sum_of_leave`): nonnegativity,
rank monotonicity, the recurrence-in-`P` form, the probability normalization, the residual bound
(block-summable via `DefectSummable`), and the leave-probability `≥ μ`.  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

lemma kernelMass_nonneg (n : ℕ) : 0 ≤ kernelMass n :=
  Finset.sum_nonneg (fun _ hm => erdosWeight_nonneg_of_mem hm)

lemma Pker_nonneg (n k : ℕ) : 0 ≤ Pker n k := by
  unfold Pker
  split_ifs with h
  · exact div_nonneg (erdosWeight_nonneg_of_lt (by omega)) (kernelMass_nonneg n)
  · exact le_refl 0

lemma rnk_mono : Monotone rnk := by
  intro a b hab
  apply Nat.floor_mono
  have : Real.sqrt (a : ℝ) ≤ Real.sqrt (b : ℝ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast hab)
  linarith

/-- Floor bounds tying `rnk n = ⌊3√n⌋` to `√n`: `rnk n ≤ 3√n < rnk n + 1`. -/
lemma rnk_sqrt_bounds (n : ℕ) :
    (rnk n : ℝ) ≤ 3 * Real.sqrt n ∧ 3 * Real.sqrt n < (rnk n : ℝ) + 1 := by
  unfold rnk
  exact ⟨Nat.floor_le (by positivity), Nat.lt_floor_add_one _⟩

/-- `rnk n ≥ 3·n₀+3` forces `n ≥ n₀` (converts eventual-in-`n` facts into `J ≤ rnk n` form). -/
lemma rnk_ge_of {n₀ n : ℕ} (h : 3 * n₀ + 3 ≤ rnk n) : n₀ ≤ n := by
  have h1 := (rnk_sqrt_bounds n).1
  have hge : (n₀ : ℝ) + 1 ≤ Real.sqrt n := by
    have hcast : (3 * n₀ + 3 : ℝ) ≤ (rnk n : ℝ) := by exact_mod_cast h
    have : (3 * (n₀ : ℝ) + 3) ≤ 3 * Real.sqrt n := by push_cast at hcast ⊢; linarith
    linarith
  have hsq : ((n₀ : ℝ) + 1) ^ 2 ≤ (n : ℝ) := by
    have hmul := mul_le_mul hge hge (by positivity) (Real.sqrt_nonneg _)
    rw [← pow_two, ← pow_two, Real.sq_sqrt (by positivity)] at hmul
    exact hmul
  have : (n₀ : ℝ) ≤ (n : ℝ) := by nlinarith [hsq]
  exact_mod_cast this

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# TASK 11: the first-entrance (run-until-hit) rank-band Doeblin engine

The fixed-step-count overlap reductions (`ErdosAlignment`, `DoeblinWalls`) are *false* for far-apart
high ranks (rank drops by `O(1)` per step, so a rank-`1000R` chain and a rank-`1001R` chain have
disjoint `L`-step laws for any fixed `L`).  This file builds the correct
device: the **first-entrance kernel** `enterBandKer P B`, which runs the chain *until* it enters a
finite rank band `B` — variable hitting time, not a fixed step count.  Two chains starting from very
different heights both descend *through* the band, and their first-entrance laws overlap.

Steps A–D (this file) are deterministic and reuse the banked Doeblin contraction
(`doeblin_average_diff_bound`) and the banked tail-oscillation engine (`tailOsc`,
`tendsto_zero_of_step_contraction`, `tendsto_of_tail_osc_to_zero`); they do **not** depend on the
hard analytic overlap sublemma (Step E).  Opus-authored.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ## Step A — the first-entrance kernel -/

/-- Defining equation of `enterBandKer` over the plain `Finset.range n`. -/
lemma enterBandKer_eq (P : ℕ → ℕ → ℝ) (B : Finset ℕ) (n z : ℕ) :
    enterBandKer P B n z
      = if n ∈ B then (if z = n then 1 else 0)
        else ∑ k ∈ Finset.range n, P n k * enterBandKer P B k z := by
  rw [enterBandKer]
  by_cases h : n ∈ B
  · simp [h]
  · rw [if_neg h, if_neg h, Finset.sum_attach (Finset.range n)
      (fun k => P n k * enterBandKer P B k z)]

variable {P : ℕ → ℕ → ℝ} {B : Finset ℕ}

/-- `enterBandKer` is nonnegative (given `P` nonnegative). -/
lemma enterBandKer_nonneg (hPnn : ∀ n k, 0 ≤ P n k) (n z : ℕ) :
    0 ≤ enterBandKer P B n z := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [enterBandKer_eq]
    by_cases h : n ∈ B
    · rw [if_pos h]; split <;> norm_num
    · rw [if_neg h]
      exact Finset.sum_nonneg (fun k hk =>
        mul_nonneg (hPnn n k) (ih k (Finset.mem_range.mp hk)))

/-! ## Step B — the entrance decomposition for `hitVal` -/

/-! ## Step C — Doeblin contraction of the entrance average (wires `doeblin_average_diff_bound`) -/

/-! ## Step D — the descending-ceiling band and the abstract engine

The *band* used by the engine is the **finite ceiling down-set** `ceilBand R A` = all states of rank
`< R + A` (truncated to the recursion's finite range).  This set is **unskippable on the way down**
(the chain can only enter it, never jump over it from above), so the first-entrance decomposition
holds with the harmonic hypothesis discharged at every off-band point (rank `≥ R + A ≥ J`).  The
landed point's rank is `< R + A`; the engine then splits the band into the in-band overlap part
`[R, R+A)` and the **overshoot** part `[0, R)`, which carries an escape mass driving the residual
oscillation.  A *fixed* band width `A` leaves a non-vanishing
escape floor (the genuine obstruction). -/

/-- `rnk k < R + A` already forces `k` into the enumeration window, so membership is rank-only. -/
lemma mem_ceilBand_iff {R A k : ℕ} :
    k ∈ ceilBand R A ↔ rnk k < R + A := by
  unfold ceilBand
  rw [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  intro hlt
  -- rnk k < R+A ⟹ 3√k < R+A ⟹ √k < (R+A)/3 ⟹ k < (R+A)²/9 < (R+A+2)²
  have hfloor : (3 : ℝ) * Real.sqrt (k : ℝ) < (R + A : ℝ) := by
    by_contra hcon
    rw [not_lt] at hcon
    have : (R + A : ℕ) ≤ rnk k := by
      unfold rnk; exact Nat.le_floor (by push_cast; linarith)
    omega
  have hsqrtnn : (0 : ℝ) ≤ Real.sqrt (k : ℝ) := Real.sqrt_nonneg _
  have hsq : (k : ℝ) < ((R + A : ℝ) / 3) ^ 2 := by
    have hsqrtlt : Real.sqrt (k : ℝ) < (R + A : ℝ) / 3 := by linarith
    have hknn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [Real.sq_sqrt hknn, hsqrtlt, hsqrtnn]
  have hub : ((R + A : ℝ) / 3) ^ 2 ≤ ((R + A + 2) ^ 2 : ℕ) := by
    push_cast
    have h0 : (0 : ℝ) ≤ (R : ℝ) + (A : ℝ) := by positivity
    nlinarith
  have : (k : ℝ) < ((R + A + 2) ^ 2 : ℕ) := lt_of_lt_of_le hsq hub
  exact_mod_cast this

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# TASK T2-ceiling, L4 core helper: the one-step entrance lower bound

For the same-ceiling value Doeblin (L4), the entrance laws from two ceiling-level values `x, y`
(`rnk x = rnk y = C`) into the band `B = ceilBand R (A R) = {rnk < C}` are compared on the in-band
slice.  The basic reduction is that the first-entrance kernel dominates the **one-step** kernel on
any in-band target `z ∈ B`:

  `Pker x z ≤ enterBandKer Pker B x z`   (for `x ∉ B`, `z ∈ B`).

(The first entrance can land at `z` directly on its first step; the remaining paths only add
nonnegative mass.)  Consequently

  `∑_{z ∈ slice} min (Pker x z) (Pker y z)
      ≤ ∑_{z ∈ slice} min (enterBandKer Pker B x z) (enterBandKer Pker B y z)`,

so a value-level overlap of the *one-step* predecessor laws on the slice transfers to the
first-entrance laws.  This file proves these two reductions; the residual analytic content of L4 is
the positive one-step value overlap `∑_{z ∈ slice} min (Pker x z) (Pker y z) ≥ β`, a two-start
value-window estimate.

NEW file; imports the banked entrance kernel and ceiling-hit cores, does not modify them.
Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-- **One-step entrance lower bound.**  If the start `x` is off the band (`x ∉ B`) and the target
`z` is in the band (`z ∈ B`) with `z < x`, then the first-entrance kernel dominates one `Pker` step:
`Pker x z ≤ enterBandKer Pker B x z`.  (The `k = z` term of the entrance recursion gives
`Pker x z · enterBandKer Pker B z z = Pker x z · 1 = Pker x z`; the rest is nonnegative.) -/
lemma Pker_le_enterBandKer {B : Finset ℕ} {x z : ℕ}
    (hxB : x ∉ B) (hzB : z ∈ B) (hzx : z < x) :
    Pker x z ≤ enterBandKer Pker B x z := by
  classical
  rw [enterBandKer_eq, if_neg hxB]
  -- isolate the k = z term
  have hzrange : z ∈ Finset.range x := Finset.mem_range.mpr hzx
  have hzz : enterBandKer Pker B z z = 1 := by
    rw [enterBandKer_eq, if_pos hzB, if_pos rfl]
  have hterm : Pker x z = Pker x z * enterBandKer Pker B z z := by rw [hzz, mul_one]
  rw [hterm]
  refine Finset.single_le_sum (f := fun k => Pker x k * enterBandKer Pker B k z) ?_ hzrange
  intro k _
  exact mul_nonneg (Pker_nonneg x k) (enterBandKer_nonneg (fun a b => Pker_nonneg a b) k z)

/-- **Slice overlap transfer.**  Over any `slice` of in-band targets (each `z ∈ slice` with `z ∈ B`
and `z < x`, `z < y`), the one-step predecessor-law overlap is dominated by the first-entrance-law
overlap.  Reduces the value-level Doeblin (L4) to a positive overlap of the one-step laws
`Pker x ·`, `Pker y ·`. -/
lemma min_Pker_le_min_enterBandKer_sum {B slice : Finset ℕ} {x y : ℕ}
    (hxB : x ∉ B) (hyB : y ∉ B)
    (hslice : ∀ z ∈ slice, z ∈ B ∧ z < x ∧ z < y) :
    ∑ z ∈ slice, min (Pker x z) (Pker y z)
      ≤ ∑ z ∈ slice, min (enterBandKer Pker B x z) (enterBandKer Pker B y z) := by
  refine Finset.sum_le_sum (fun z hz => ?_)
  obtain ⟨hzB, hzx, hzy⟩ := hslice z hz
  exact min_le_min (Pker_le_enterBandKer hxB hzB hzx) (Pker_le_enterBandKer hyB hzB hzy)

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# TASK T2.2: the offset law, its exponential escape tail, and the coupling overlap

The engine consumes two facts about the first-crossing **offset law** of the renewal process into a
ceiling, from two delays:

* **escape tail**: the offset exceeds `A` with probability `≤ T A`, where `T A → 0`;
* **overlap**: the two offset laws share a uniformly-positive common part on a fixed top slice.

This file:

1. defines the offset law `offsetLaw p n r r'` = `resKer p n r r'` viewed as the law of the residual
   after `n` unit-level steps from delay `r` (the residual *is* the first-crossing offset when the
   ceiling is `n` levels above the start `r`);
2. proves the **escape tail** `∑'_{r' > A} resKer p n 0 r' ≤ p((A,∞))` from any *renewal* start
   (residual `0`) — rigorously, from the increment exponential tail (the offset can exceed `A` only
   if the crossing increment exceeds `A`);
3. proves the **descent-step overlap minorization**: from delays one renewal apart, the laws
   share mass `≥ p 1` on the slice `{0}` (the increment-`1` minorization), giving `δ`;
4. states the **homogeneous renewal overlap/escape** consequence the engine needs, reducing the
   *uniform-in-delay* overlap to the renewal coalescence fact (the irreducible analytic input).

Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Renewal

/-! ## The increment tail and its exponential bound. -/

/-! ## The stationary offset law (size-biased / residual law).

The residual chain's stationary distribution is `π r' = incrTail p r' / μ`, where
`μ = ∑'_{r'} incrTail p r' = ∑' d, d · p d = E[increment]` is the mean increment.  We build `π`,
prove it is a probability mass (`∑' π = 1`), that it has uniformly-positive mass at the slice `{0}`
(`π 0 = 1/μ > 0`), and that its tail beyond `A` vanishes.  These are precisely the
slice-overlap-floor and escape-vanishing facts the engine needs from the *limiting* offset law.  -/

/-! ## The first-crossing offset law from a delay, and its delay-independence.

The renewal process started at residual (= delay) `s` to the ceiling descends deterministically to a
renewal epoch (residual `0`) in exactly `s` unit-level steps, then draws one increment.  The offset
of the first crossing *after that renewal* is therefore distributed as `p(·+1)` — the increment law
shifted by one — **independently of the delay `s`** (`resKer_descent_then_step`).  This delay-
independence is the engine's coupling: two crossings from two different delays, each measured at its
own first post-descent renewal, share the *identical* offset law, so their common mass on a fixed top
slice is a fixed positive number and is not diluted by widening the band. -/

/-! ## Escape tail of the offset law. -/

/-! ## Common overlap mass of two offset laws on a fixed top slice. -/

/-! ## T2.2 — the homogeneous renewal uniform overshoot/overlap theorem.

Packages the three facts the engine consumes, for an aperiodic exponential-tail integer renewal law:

* a fixed top-slice width `B := 1` and overlap floor `δ := p 1 > 0`, uniform over both delays and over
  the band width `A`;
* a vanishing escape majorant `T A := incrTail p A → 0`;
* for every band width `A ≥ B` and any two delays `s, s'`: the common mass of the two first-crossing
  offset laws on the slice `{0,…,B−1}` is `≥ δ`, and each offset law's escape beyond `A` is `≤ T A`.

The hypotheses `hp_tail`, `hp_aper.2` (i.e. `p 2 > 0`) are recorded for the downstream T2.1/T2.3
interface (the exponential tail certifies the explicit rate; `p 2 > 0` certifies true aperiodicity of
the support, gcd = 1) but the engine-facing overlap/escape pair already follows from `p 1 > 0` and
summability via the delay-independence of the post-renewal offset law. -/

/-! ## Engine-facing bridge: overlap from a uniform single-state minorization.

The variable rank-band engine consumes the overlap as
`δ ≤ ∑_{z ∈ slice} min (κ n z) (κ n' z)` where `κ = enterBandKer Pker (ceilBand …)` and `slice` is
the in-band top slice.  The genuine analytic input is a uniform
*single-state minorization* `κ n z ≥ η` for the two starts on a fixed nonempty subset `S` of the
slice (a Doeblin minorization at the common ceiling).  Once that minorization exists, the overlap is
purely combinatorial: `min (κ n z) (κ n' z) ≥ η` on `S`, so the overlap is `≥ η · |S|`.

This lemma isolates that combinatorial step so the (remaining) analytic minorization plugs straight
into the engine.  It depends on NEITHER the false rank-drop local limit NOR any renewal limit. -/

/-- **Overlap from minorization (engine-facing, abstract).**  If a kernel `κ` is `≥ η` at both starts
`n, n'` on every state of a finite set `S` that is contained in the engine's filtered slice
`slice = T.filter q`, then the engine overlap over that slice is `≥ η · |S|`.  (We bound the slice sum
below by its `S`-part; off-`S` summands are nonnegative because `κ ≥ 0`.) -/
lemma overlap_ge_of_minorization
    {κ : ℕ → ℕ → ℝ} {T : Finset ℕ} {q : ℕ → Prop} [DecidablePred q]
    {S : Finset ℕ} {n n' : ℕ} {η : ℝ}
    (hSslice : S ⊆ T.filter q)
    (hκnn : ∀ z, 0 ≤ κ n z) (hκnn' : ∀ z, 0 ≤ κ n' z)
    (hmin : ∀ z ∈ S, η ≤ κ n z ∧ η ≤ κ n' z) :
    (η * S.card : ℝ) ≤ ∑ z ∈ T.filter q, min (κ n z) (κ n' z) := by
  classical
  -- the slice sum dominates its S-part (off-S terms are min of nonnegatives ≥ 0)
  have hSpart : ∑ z ∈ S, min (κ n z) (κ n' z) ≤ ∑ z ∈ T.filter q, min (κ n z) (κ n' z) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSslice
    intro z _ _; exact le_min (hκnn z) (hκnn' z)
  -- on S, each min ≥ η
  have hSlb : (η * S.card : ℝ) ≤ ∑ z ∈ S, min (κ n z) (κ n' z) := by
    have hconst : ∑ _z ∈ S, η = η * S.card := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rw [← hconst]
    apply Finset.sum_le_sum
    intro z hz
    obtain ⟨h1, h2⟩ := hmin z hz
    exact le_min h1 h2
  linarith

end AnalyticCombinatorics.Ch8.Partitions.Renewal
end
end

/-!
# TASK L4 (R8 elementary route): same-ceiling value overlap via the divisor-self bound `σ(m) ≥ m`

The variable rank-band engine needs a positive in-band overlap (L4): for two starts `x, y` at the
same ceiling rank `T = R + A R`, the first-entrance laws into the band `ceilBand R (A R)` overlap by
`≥ β` on the in-band slice `{R ≤ rnk z}`.  By the banked one-step reduction
`min_Pker_le_min_enterBandKer_sum` this reduces to a positive overlap of the **one-step** predecessor
laws `Pker x ·`, `Pker y ·` on the slice.

R8's elementary idea (`/tmp/ac_a_uniform.txt`): a single **common value window**
`W_T = [ (T+1)²/9 − 2T , T²/9 − T ] ∩ ℕ` (length `~7T/9`) sits below every ceiling-rank value `x`,
inside the engine slice, and carries `Pker x z ≥ c/T` for EVERY same-ceiling `x` and `z ∈ W_T`.
The lower bound uses ONLY the trivial divisor-self bound `σ(x−z) ≥ x−z ≥ T` (no two-point divisor
estimate, no `KernelWindow`).  A constant minorant `η = c/T` on `S = W_T` with `|W_T| ≥ q·T` gives
overlap `≥ (c/T)(q·T) = cq =: β > 0` via the banked `overlap_ge_of_minorization`.

NEW file; imports the banked bricks, does not modify them.  Opus-authored.
-/

noncomputable section

open Filter Topology BigOperators

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

/-! ## Brick 1 — the divisor-self bound `σ(m) ≥ m`. -/

/-- **Divisor-self lower bound.**  `m ≤ σ(m)` for `1 ≤ m`: the divisor `m ∣ m` is a single term of
the nonnegative divisor sum `σ(m) = ∑_{d ∣ m} d`. -/
lemma sigmaR_ge_self {m : ℕ} (hm : 1 ≤ m) : (m : ℝ) ≤ Sigma.sigmaR m := by
  rw [Sigma.sigmaR_eq_sum_divisors]
  have hmem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have h := Finset.single_le_sum (f := fun d : ℕ => (d : ℝ))
    (fun d _ => Nat.cast_nonneg d) hmem
  simpa using h


/-! ## Brick 2 — the common value window. -/

/-- **Common value window** `W_T = Icc ((T+1)²/9 − 2T) (T²/9 − T)` (nat division).  Length `~7T/9`;
sits below every ceiling-rank-`T` value and inside the in-band slice. -/
def commonValueWindow (T : ℕ) : Finset ℕ :=
  Finset.Icc ((T + 1) ^ 2 / 9 - 2 * T) (T ^ 2 / 9 - T)

/-- Cast bounds for nat division by `9`: `↑n/9 − 1 < ↑(n/9) ≤ ↑n/9`. -/
lemma cast_div9_bounds (n : ℕ) :
    (n : ℝ) / 9 - 1 < ((n / 9 : ℕ) : ℝ) ∧ ((n / 9 : ℕ) : ℝ) ≤ (n : ℝ) / 9 := by
  constructor
  · have hdm := Nat.div_add_mod n 9
    have hmod : n % 9 < 9 := Nat.mod_lt n (by norm_num)
    have h : n < 9 * (n / 9) + 9 := by omega
    have hc : (n : ℝ) < 9 * ((n / 9 : ℕ) : ℝ) + 9 := by exact_mod_cast h
    linarith
  · exact Nat.cast_div_le

/-! ## Brick 3 — window geometry: jump and sqrt bounds. -/

set_option maxHeartbeats 800000 in
/-- **Window geometry.**  Eventually in `T`, for every value `x` of rank exactly `T` and every `z` in
the common window: `1 ≤ z`, `z < x`, the jump satisfies `T ≤ x − z ≤ 3T`, and `√x − √z ≤ 10`. -/
lemma commonValueWindow_jump_bounds :
    ∀ᶠ T in atTop, ∀ x z, rnk x = T → z ∈ commonValueWindow T →
      1 ≤ z ∧ z < x ∧
      (T : ℝ) ≤ ((x - z : ℕ) : ℝ) ∧
      ((x - z : ℕ) : ℝ) ≤ 3 * (T : ℝ) ∧
      Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ) ≤ 10 := by
  filter_upwards [eventually_ge_atTop 100] with T hT100
  intro x z hx hz
  -- unpack rank: T²/9 ≤ x < (T+1)²/9 (real), via rnk x = T
  have hTR : (100 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT100
  -- rnk x = T  ⟹  T ≤ 3√x < T+1
  have hxb := rnk_sqrt_bounds x
  rw [hx] at hxb
  obtain ⟨hxlo, hxhi⟩ := hxb        -- T ≤ 3√x ,  3√x < T+1
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    have hsx : (0 : ℝ) < Real.sqrt (x : ℝ) := by
      have : (T : ℝ) / 3 ≤ Real.sqrt (x : ℝ) := by linarith
      linarith
    have := Real.sqrt_pos.mp hsx; linarith
  -- √x ≥ T/3 and √x < (T+1)/3
  have hsx_lo : (T : ℝ) / 3 ≤ Real.sqrt (x : ℝ) := by linarith
  have hsx_hi : Real.sqrt (x : ℝ) < ((T : ℝ) + 1) / 3 := by linarith
  -- x bounds: T²/9 ≤ x and x < (T+1)²/9
  have hsxsq : Real.sqrt (x : ℝ) ^ 2 = (x : ℝ) := Real.sq_sqrt hxpos.le
  have hx_lo : (T : ℝ) ^ 2 / 9 ≤ (x : ℝ) := by
    have hmm := mul_le_mul hsx_lo hsx_lo (by positivity) (Real.sqrt_nonneg _)
    nlinarith [hmm, hsxsq]
  have hx_hi : (x : ℝ) < ((T : ℝ) + 1) ^ 2 / 9 := by
    have hsxnn : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
    nlinarith [hsxsq, hsx_hi, hsxnn]
  -- window membership: aT ≤ z ≤ bT  (nat), with aT = (T+1)²/9 − 2T, bT = T²/9 − T
  rw [commonValueWindow, Finset.mem_Icc] at hz
  obtain ⟨hza, hzb⟩ := hz
  -- real bounds on aT, bT
  obtain ⟨hd1lo, hd1hi⟩ := cast_div9_bounds ((T + 1) ^ 2)
  obtain ⟨hd2lo, hd2hi⟩ := cast_div9_bounds (T ^ 2)
  -- 2T ≤ (T+1)²/9 and T ≤ T²/9 (so nat subs are genuine, casts behave)
  have h2T_le : 2 * T ≤ (T + 1) ^ 2 / 9 := by
    have : 18 * T ≤ (T + 1) ^ 2 := by nlinarith [hT100]
    omega
  have hT_le : T ≤ T ^ 2 / 9 := by
    have : 9 * T ≤ T ^ 2 := by nlinarith [hT100]
    omega
  -- cast the nat endpoints
  -- real lower bound on ↑((T+1)²/9)
  have hd1lo' : ((T : ℝ) + 1) ^ 2 / 9 - 1 ≤ (((T + 1) ^ 2 / 9 : ℕ) : ℝ) := by
    have he : (((T + 1) ^ 2 : ℕ) : ℝ) = ((T : ℝ) + 1) ^ 2 := by push_cast; ring
    rw [he] at hd1lo; linarith
  -- real upper bound on ↑(T²/9)
  have hd2hi' : (((T ^ 2 / 9 : ℕ)) : ℝ) ≤ (T : ℝ) ^ 2 / 9 := by
    have he : (((T ^ 2 : ℕ)) : ℝ) = (T : ℝ) ^ 2 := by push_cast; ring
    rw [he] at hd2hi; linarith
  have hza_real : ((T : ℝ) + 1) ^ 2 / 9 - 1 - 2 * (T : ℝ) ≤ (z : ℝ) := by
    have hzaR : (((T + 1) ^ 2 / 9 : ℕ) : ℝ) - 2 * (T : ℝ) ≤ (z : ℝ) := by
      have hc : (((T + 1) ^ 2 / 9 - 2 * T : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast hza
      rwa [Nat.cast_sub h2T_le, Nat.cast_mul, Nat.cast_ofNat] at hc
    linarith
  have hzb_real : (z : ℝ) ≤ (T : ℝ) ^ 2 / 9 - (T : ℝ) := by
    have hzbR : (z : ℝ) ≤ (((T ^ 2 / 9 : ℕ)) : ℝ) - (T : ℝ) := by
      have hc : (z : ℝ) ≤ (((T ^ 2 / 9 - T : ℕ)) : ℝ) := by exact_mod_cast hzb
      rwa [Nat.cast_sub hT_le] at hc
    linarith
  -- z < x
  have hzltx : z < x := by
    have : (z : ℝ) < (x : ℝ) := by
      have : (z : ℝ) ≤ (T : ℝ) ^ 2 / 9 - T := hzb_real
      have hTge1 : (1 : ℝ) ≤ (T : ℝ) := by linarith
      nlinarith [hx_lo, this, hTge1]
    exact_mod_cast this
  -- 1 ≤ z
  have h1z : 1 ≤ z := by
    have : (1 : ℝ) ≤ (z : ℝ) := by
      have hlb : ((T : ℝ) + 1) ^ 2 / 9 - 1 - 2 * (T : ℝ) ≤ (z : ℝ) := hza_real
      nlinarith [hlb, hTR]
    exact_mod_cast this
  -- jump bounds in ℝ via (x - z : ℕ) = x - z
  have hsub_cast : ((x - z : ℕ) : ℝ) = (x : ℝ) - (z : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hzltx)]
  refine ⟨h1z, hzltx, ?_, ?_, ?_⟩
  · -- x − z ≥ T : x ≥ T²/9, z ≤ T²/9 − T
    rw [hsub_cast]; linarith [hx_lo, hzb_real]
  · -- x − z ≤ 3T : x < (T+1)²/9, z ≥ (T+1)²/9 − 1 − 2T  ⟹ x − z < 2T + 1 ≤ 3T
    rw [hsub_cast]
    have hdiff : (x : ℝ) - (z : ℝ) < 2 * (T : ℝ) + 1 := by
      linarith [hx_hi, hza_real]
    linarith [hdiff, hTR]
  · -- √x − √z ≤ 10 :  ≤ (x − z)/√x ≤ (2T+1)/(T/3) ≤ 7 ≤ 10
    have hsz_nn : 0 ≤ Real.sqrt (z : ℝ) := Real.sqrt_nonneg _
    have hsx_pos : 0 < Real.sqrt (x : ℝ) := by
      have : (T : ℝ) / 3 ≤ Real.sqrt (x : ℝ) := hsx_lo; linarith
    -- (√x − √z)(√x + √z) = x − z
    have hszsq : Real.sqrt (z : ℝ) ^ 2 = (z : ℝ) := Real.sq_sqrt (by positivity)
    have hprod : (Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ)) * (Real.sqrt (x : ℝ) + Real.sqrt (z : ℝ))
        = (x : ℝ) - (z : ℝ) := by nlinarith [hsxsq, hszsq]
    have hxz_ub : (x : ℝ) - (z : ℝ) < 2 * (T : ℝ) + 1 := by
      linarith [hx_hi, hza_real]
    -- √x + √z ≥ √x ≥ T/3
    have hsum_lo : (T : ℝ) / 3 ≤ Real.sqrt (x : ℝ) + Real.sqrt (z : ℝ) := by linarith [hsx_lo, hsz_nn]
    have hgap_nn : 0 ≤ Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ) := by
      have hle : Real.sqrt (z : ℝ) ≤ Real.sqrt (x : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast le_of_lt hzltx)
      linarith
    -- gap·(T/3) ≤ gap·sum = x−z < 2T+1, so gap·T < 6T+3, gap < 7 ≤ 10
    set g := Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ) with hgdef
    set s := Real.sqrt (x : ℝ) + Real.sqrt (z : ℝ) with hsdef
    have hgs : g * s < 2 * (T : ℝ) + 1 := by rw [hprod]; exact hxz_ub
    have hgT : g * ((T : ℝ) / 3) ≤ g * s := by
      apply mul_le_mul_of_nonneg_left hsum_lo hgap_nn
    have hgT2 : g * (T : ℝ) < 6 * (T : ℝ) + 3 := by nlinarith [hgT, hgs]
    nlinarith [hgT2, hTR, hgap_nn]


/-! ## Brick 4 — the window lies in the in-band slice. -/

set_option maxHeartbeats 800000 in
/-- **Window ⊆ in-band slice.**  For a growing band width `A` (`A R → ∞`), eventually in `R` every
`z` in the window of the ceiling rank `T = R + A R` satisfies `R ≤ rnk z < T`, i.e. lies in the
engine slice `(ceilBand R (A R)).filter (R ≤ rnk ·)`. -/
lemma commonValueWindow_subset_slice (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
    ∀ᶠ R in atTop, ∀ z, z ∈ commonValueWindow (R + A R) →
      z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z) := by
  -- A R ≥ 9 eventually, and R + A R ≥ 45 eventually (since A R → ∞)
  have hA9 : ∀ᶠ R in atTop, 9 ≤ A R := hA (eventually_ge_atTop 9)
  filter_upwards [hA9, eventually_ge_atTop 45] with R hA9R hR45
  intro z hz
  set T := R + A R with hTdef
  have hT45 : 45 ≤ T := by omega
  have hTR : (45 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT45
  rw [commonValueWindow, Finset.mem_Icc] at hz
  obtain ⟨hza, hzb⟩ := hz
  -- real endpoint bounds (same casts as brick 3)
  obtain ⟨hd1lo, _⟩ := cast_div9_bounds ((T + 1) ^ 2)
  obtain ⟨_, hd2hi⟩ := cast_div9_bounds (T ^ 2)
  have h2T_le : 2 * T ≤ (T + 1) ^ 2 / 9 := by
    have : 18 * T ≤ (T + 1) ^ 2 := by nlinarith [hTR]
    omega
  have hT_le : T ≤ T ^ 2 / 9 := by
    have : 9 * T ≤ T ^ 2 := by nlinarith [hTR]
    omega
  have hd1lo' : ((T : ℝ) + 1) ^ 2 / 9 - 1 ≤ (((T + 1) ^ 2 / 9 : ℕ) : ℝ) := by
    have he : (((T + 1) ^ 2 : ℕ) : ℝ) = ((T : ℝ) + 1) ^ 2 := by push_cast; ring
    rw [he] at hd1lo; linarith
  have hd2hi' : (((T ^ 2 / 9 : ℕ)) : ℝ) ≤ (T : ℝ) ^ 2 / 9 := by
    have he : (((T ^ 2 : ℕ)) : ℝ) = (T : ℝ) ^ 2 := by push_cast; ring
    rw [he] at hd2hi; linarith
  have hza_real : ((T : ℝ) + 1) ^ 2 / 9 - 1 - 2 * (T : ℝ) ≤ (z : ℝ) := by
    have hzaR : (((T + 1) ^ 2 / 9 : ℕ) : ℝ) - 2 * (T : ℝ) ≤ (z : ℝ) := by
      have hc : (((T + 1) ^ 2 / 9 - 2 * T : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast hza
      rwa [Nat.cast_sub h2T_le, Nat.cast_mul, Nat.cast_ofNat] at hc
    linarith
  have hzb_real : (z : ℝ) ≤ (T : ℝ) ^ 2 / 9 - (T : ℝ) := by
    have hzbR : (z : ℝ) ≤ (((T ^ 2 / 9 : ℕ)) : ℝ) - (T : ℝ) := by
      have hc : (z : ℝ) ≤ (((T ^ 2 / 9 - T : ℕ)) : ℝ) := by exact_mod_cast hzb
      rwa [Nat.cast_sub hT_le] at hc
    linarith
  have hznn : (0 : ℝ) ≤ (z : ℝ) := Nat.cast_nonneg z
  -- rnk z < T : 3√z < T from z < T²/9
  have hrnk_lt : rnk z < T := by
    unfold rnk
    have hsz : 3 * Real.sqrt (z : ℝ) < (T : ℝ) := by
      have hzlt : (z : ℝ) < (T : ℝ) ^ 2 / 9 := by linarith [hzb_real, hTR]
      have hsqlt : Real.sqrt (z : ℝ) < (T : ℝ) / 3 := by
        rw [show (T : ℝ) / 3 = Real.sqrt (((T : ℝ) / 3) ^ 2) by
          rw [Real.sqrt_sq (by positivity)]]
        apply Real.sqrt_lt_sqrt hznn
        nlinarith [hzlt]
      linarith
    have : (⌊3 * Real.sqrt (z : ℝ)⌋₊ : ℝ) ≤ 3 * Real.sqrt (z : ℝ) := Nat.floor_le (by positivity)
    have hfl : (⌊3 * Real.sqrt (z : ℝ)⌋₊ : ℝ) < (T : ℝ) := by linarith
    exact_mod_cast hfl
  -- R ≤ rnk z : 3√z ≥ T − 9 ≥ R from z ≥ (T+1)²/9 − 2T − 1
  have hR_le : R ≤ rnk z := by
    have hRle : R ≤ T - 9 := by omega
    refine le_trans hRle ?_
    unfold rnk
    apply Nat.le_floor
    -- need (T − 9 : ℝ) ≤ 3√z, i.e. 9z ≥ (T−9)²
    have h9z : (T : ℝ) ^ 2 - 16 * (T : ℝ) - 8 ≤ 9 * (z : ℝ) := by
      have : 9 * (((T : ℝ) + 1) ^ 2 / 9 - 1 - 2 * (T : ℝ)) ≤ 9 * (z : ℝ) := by linarith [hza_real]
      nlinarith [this]
    have hsq : ((T - 9 : ℕ) : ℝ) ^ 2 ≤ 9 * (z : ℝ) := by
      have hcast : ((T - 9 : ℕ) : ℝ) = (T : ℝ) - 9 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [hcast]
      nlinarith [h9z, hTR]
    -- (T−9) ≤ 3√z  ⟸  (T−9)² ≤ 9z = (3√z)²
    have hszsq : (3 * Real.sqrt (z : ℝ)) ^ 2 = 9 * (z : ℝ) := by
      rw [mul_pow]; rw [Real.sq_sqrt hznn]; ring
    have hTm9nn : (0 : ℝ) ≤ ((T - 9 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3snn : (0 : ℝ) ≤ 3 * Real.sqrt (z : ℝ) := by positivity
    nlinarith [hsq, hszsq, hTm9nn, h3snn]
  rw [Finset.mem_filter]
  exact ⟨mem_ceilBand_iff.mpr hrnk_lt, hR_le⟩


/-! ## Brick 5 — pointwise `Pker` lower bound on the window. -/

set_option maxHeartbeats 1000000 in
/-- **Pointwise `Pker` lower bound.**  There is `c > 0` so that eventually in the ceiling rank `T`,
for every value `x` of rank `T` and every `z` in the common window, `c/T ≤ Pker x z`.  Uses only the
divisor-self bound `σ(x−z) ≥ x−z ≥ T`, the window upper bound `z ≤ T²/9`, the sqrt-gap bound
`√x−√z ≤ 10`, and the eventual `kernelMass x ≤ 2`. -/
lemma Pker_commonValueWindow_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T in atTop, ∀ x z, rnk x = T → z ∈ commonValueWindow T →
      c / (T : ℝ) ≤ Pker x z := by
  obtain ⟨K, hKpos, hKev⟩ := kernelMass_sub_one_rate
  -- eventual K/n ≤ 1/2 ⟹ kernelMass ∈ [1/2, 3/2] ⊆ (0,2]
  have hhalf : ∀ᶠ n : ℕ in atTop, K / (n : ℝ) ≤ 1 / 2 := by
    have htend : Tendsto (fun n : ℕ => K / (n : ℝ)) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop)
    exact htend.eventually_le_const (by norm_num)
  obtain ⟨Nkm, hNkm⟩ := eventually_atTop.1 (hKev.and hhalf)
  obtain ⟨Tj, hTj⟩ := eventually_atTop.1 commonValueWindow_jump_bounds
  refine ⟨(9 / 2) * Real.exp (-(10 * C)), by positivity, ?_⟩
  -- choose T large: ≥ 100 (jump), ≥ Tj, and rnk x = T forces x ≥ Nkm
  filter_upwards [eventually_ge_atTop (max (max 100 Tj) (3 * Nkm + 3))] with T hTbig
  intro x z hx hz
  have hT100 : 100 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTbig
  have hTjle : Tj ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTbig
  have hTR : (100 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT100
  have hTpos : (0 : ℝ) < (T : ℝ) := by linarith
  -- jump/geometry facts
  obtain ⟨h1z, hzltx, hjlo, _hjhi, hsqrt⟩ := hTj T hTjle x z hx hz
  -- x ≥ Nkm (from rnk x = T and T large)
  have hxge : Nkm ≤ x := by
    apply rnk_ge_of (n₀ := Nkm)
    rw [hx]
    have : 3 * Nkm + 3 ≤ T := le_trans (le_max_right _ _) hTbig
    omega
  obtain ⟨hKx, hhalfx⟩ := hNkm x hxge
  have hxR : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
  have hxpos : (0 : ℝ) < (x : ℝ) := by linarith
  obtain ⟨hSlo, hSup⟩ := abs_le.1 hKx
  have hS2 : kernelMass x ≤ 2 := by linarith [hSup, hhalfx]
  have hSpos : (0 : ℝ) < kernelMass x := by linarith [hSlo, hhalfx]
  -- z and (x−z) bounds
  have hzR : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast h1z
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith
  -- z ≤ T²/9  (from window upper edge)
  have hz_ub : (z : ℝ) ≤ (T : ℝ) ^ 2 / 9 := by
    rw [commonValueWindow, Finset.mem_Icc] at hz
    obtain ⟨_, hzb⟩ := hz
    obtain ⟨_, hd2hi⟩ := cast_div9_bounds (T ^ 2)
    have hT_le : T ≤ T ^ 2 / 9 := by
      have : 9 * T ≤ T ^ 2 := by nlinarith [hTR]
      omega
    have hd2hi' : (((T ^ 2 / 9 : ℕ)) : ℝ) ≤ (T : ℝ) ^ 2 / 9 := by
      have he : (((T ^ 2 : ℕ)) : ℝ) = (T : ℝ) ^ 2 := by push_cast; ring
      rw [he] at hd2hi; linarith
    have hzbR : (z : ℝ) ≤ (((T ^ 2 / 9 : ℕ)) : ℝ) - (T : ℝ) := by
      have hc : (z : ℝ) ≤ (((T ^ 2 / 9 - T : ℕ)) : ℝ) := by exact_mod_cast hzb
      rwa [Nat.cast_sub hT_le] at hc
    linarith
  -- expand Pker
  have hPeq : Pker x z = erdosWeight x (x - z) / kernelMass x := by
    unfold Pker; rw [if_pos ⟨h1z, hzltx⟩]
  -- erdosWeight x (x−z) = σ(x−z)/z · exp(−C(√x − √z))   [since x − (x−z) = z]
  have hxsub : x - (x - z) = z := by omega
  have hew : erdosWeight x (x - z)
      = Sigma.sigmaR (x - z) / (z : ℝ) * Real.exp (-C * (Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ))) := by
    unfold erdosWeight
    rw [hxsub]
  -- σ(x−z) ≥ T
  have hsig : (T : ℝ) ≤ Sigma.sigmaR (x - z) := by
    have h1 : 1 ≤ x - z := by omega
    exact le_trans hjlo (sigmaR_ge_self (m := x - z) h1)
  -- exponential factor ≥ exp(−10C)
  have hexp : Real.exp (-(10 * C)) ≤ Real.exp (-C * (Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hCpos := C_pos
    nlinarith [hsqrt, hCpos]
  -- erdosWeight ≥ (T/z)·exp(−10C) ≥ (9/T)·exp(−10C)
  have hew_lb : (9 / (T : ℝ)) * Real.exp (-(10 * C)) ≤ erdosWeight x (x - z) := by
    rw [hew]
    have hsigz : (T : ℝ) / (z : ℝ) ≤ Sigma.sigmaR (x - z) / (z : ℝ) := by
      gcongr
    have hTz : (9 : ℝ) / (T : ℝ) ≤ (T : ℝ) / (z : ℝ) := by
      rw [div_le_div_iff₀ hTpos hzpos]
      nlinarith [hz_ub, hTpos]
    have hch : (9 / (T : ℝ)) ≤ Sigma.sigmaR (x - z) / (z : ℝ) := le_trans hTz hsigz
    have hexpnn : (0 : ℝ) ≤ Real.exp (-(10 * C)) := (Real.exp_pos _).le
    calc (9 / (T : ℝ)) * Real.exp (-(10 * C))
        ≤ (Sigma.sigmaR (x - z) / (z : ℝ)) * Real.exp (-(10 * C)) :=
          mul_le_mul_of_nonneg_right hch hexpnn
      _ ≤ (Sigma.sigmaR (x - z) / (z : ℝ))
            * Real.exp (-C * (Real.sqrt (x : ℝ) - Real.sqrt (z : ℝ))) := by
          apply mul_le_mul_of_nonneg_left hexp
          exact div_nonneg (sigmaR_nonneg _) hzpos.le
  -- divide by kernelMass x ≤ 2
  rw [hPeq, le_div_iff₀ hSpos]
  -- goal:  (9/2)·exp(−10C)/T · kernelMass x ≤ erdosWeight x (x−z)
  calc (9 / 2) * Real.exp (-(10 * C)) / (T : ℝ) * kernelMass x
      ≤ (9 / 2) * Real.exp (-(10 * C)) / (T : ℝ) * 2 := by
        apply mul_le_mul_of_nonneg_left hS2
        positivity
    _ = (9 / (T : ℝ)) * Real.exp (-(10 * C)) := by
          rw [div_mul_eq_mul_div]; field_simp
    _ ≤ erdosWeight x (x - z) := hew_lb


/-! ## Brick 6 — linear cardinality of the window. -/

set_option maxHeartbeats 800000 in
/-- **Linear window cardinality.**  `(1/2)·T ≤ |W_T|` eventually (the real window length is
`(7T−1)/9`, so any `q < 7/9` works; `q = 1/2` with margin). -/
lemma commonValueWindow_card_linear :
    ∀ᶠ T : ℕ in atTop, (1 / 2 : ℝ) * (T : ℝ) ≤ ((commonValueWindow T).card : ℝ) := by
  filter_upwards [eventually_ge_atTop 100] with T hT100
  have hTR : (100 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT100
  -- nat sub validity
  have h2T_le : 2 * T ≤ (T + 1) ^ 2 / 9 := by
    have : 18 * T ≤ (T + 1) ^ 2 := by nlinarith [hTR]
    omega
  have hT_le : T ≤ T ^ 2 / 9 := by
    have : 9 * T ≤ T ^ 2 := by nlinarith [hTR]
    omega
  -- cast bounds
  obtain ⟨hd1lo, hd1hi⟩ := cast_div9_bounds ((T + 1) ^ 2)
  obtain ⟨hd2lo, hd2hi⟩ := cast_div9_bounds (T ^ 2)
  rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one] at hd1lo hd1hi
  rw [Nat.cast_pow] at hd2lo hd2hi
  -- real bounds on a, b
  have ha_ub : (((T + 1) ^ 2 / 9 - 2 * T : ℕ) : ℝ) ≤ ((T : ℝ) + 1) ^ 2 / 9 - 2 * (T : ℝ) := by
    rw [Nat.cast_sub h2T_le, Nat.cast_mul, Nat.cast_ofNat]; linarith [hd1hi]
  have hb_lb : (T : ℝ) ^ 2 / 9 - 1 - (T : ℝ) ≤ (((T ^ 2 / 9 - T : ℕ)) : ℝ) := by
    rw [Nat.cast_sub hT_le]; linarith [hd2lo]
  -- a ≤ b (so Icc nonempty)
  have hab : (T + 1) ^ 2 / 9 - 2 * T ≤ T ^ 2 / 9 - T := by
    have hr : (((T + 1) ^ 2 / 9 - 2 * T : ℕ) : ℝ) ≤ (((T ^ 2 / 9 - T : ℕ)) : ℝ) := by
      nlinarith [ha_ub, hb_lb, hTR]
    exact_mod_cast hr
  -- card = b + 1 − a
  rw [commonValueWindow, Nat.card_Icc]
  have hcard_cast : ((T ^ 2 / 9 - T + 1 - ((T + 1) ^ 2 / 9 - 2 * T) : ℕ) : ℝ)
      = (((T ^ 2 / 9 - T : ℕ)) : ℝ) + 1 - (((T + 1) ^ 2 / 9 - 2 * T : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  rw [hcard_cast]
  -- (b+1−a) ≥ (T²/9 − 1 − T) + 1 − ((T+1)²/9 − 2T) = (7T−1)/9 ≥ T/2
  nlinarith [ha_ub, hb_lb, hTR]


/-! ## Brick 7 — one-step same-ceiling value overlap. -/

/-- The ceiling rank `R ↦ R + A R` tends to `atTop` (since `R + A R ≥ R`). -/
lemma ceilRank_tendsto (A : ℕ → ℕ) : Tendsto (fun R => R + A R) atTop atTop :=
  tendsto_atTop_mono (fun R => Nat.le_add_right R (A R)) tendsto_id

section
end

set_option maxHeartbeats 800000 in
/-- **One-step same-ceiling value overlap (L4 one-step form).**  There is `β > 0` so that eventually
in `R`, any two values `x, y` of the ceiling rank `T = R + A R` have one-step predecessor overlap
`≥ β` on the in-band slice.  Via `overlap_ge_of_minorization` with the uniform window minorant
`η = c/T` (brick 5) on `S = commonValueWindow T` of card `≥ T/2` (brick 6), inside the slice
(brick 4):  `η·|S| ≥ (c/T)(T/2) = c/2 =: β`. -/
lemma Pker_same_ceiling_oneStep_overlap (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
    ∃ β : ℝ, 0 < β ∧
      ∀ᶠ R in atTop, ∀ x y, rnk x = R + A R → rnk y = R + A R →
        β ≤ ∑ z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z),
              min (Pker x z) (Pker y z) := by
  obtain ⟨c, hcpos, hclow⟩ := Pker_commonValueWindow_lower
  refine ⟨c / 2, by positivity, ?_⟩
  have htend := ceilRank_tendsto A
  -- pull the T-eventual facts (brick 5, brick 6) to R-eventual along T = R + A R
  have hlowR : ∀ᶠ R in atTop, ∀ x z, rnk x = R + A R → z ∈ commonValueWindow (R + A R) →
      c / ((R + A R : ℕ) : ℝ) ≤ Pker x z := htend.eventually hclow
  have hcardR : ∀ᶠ R in atTop, (1 / 2 : ℝ) * ((R + A R : ℕ) : ℝ)
      ≤ ((commonValueWindow (R + A R)).card : ℝ) := htend.eventually commonValueWindow_card_linear
  have hsliceR := commonValueWindow_subset_slice A hA
  have hTposR : ∀ᶠ R : ℕ in atTop, (0 : ℝ) < ((R + A R : ℕ) : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with R hR
    have : (1 : ℝ) ≤ ((R + A R : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ R + A R)
    linarith
  filter_upwards [hlowR, hcardR, hsliceR, hTposR] with R hlow hcard hslice hTpos
  intro x y hx hy
  set T : ℕ := R + A R with hTdef
  -- minorant η = c/T on S = commonValueWindow T
  have hmin : ∀ z ∈ commonValueWindow T, c / (T : ℝ) ≤ Pker x z ∧ c / (T : ℝ) ≤ Pker y z := by
    intro z hz
    exact ⟨hlow x z hx hz, hlow y z hy hz⟩
  have hov := Renewal.overlap_ge_of_minorization
    (κ := Pker) (T := ceilBand R (A R)) (q := fun z => R ≤ rnk z)
    (S := commonValueWindow T) (n := x) (n' := y) (η := c / (T : ℝ))
    hslice (fun z => Pker_nonneg x z) (fun z => Pker_nonneg y z) hmin
  -- (c/T)·|S| ≥ (c/T)·(T/2) = c/2
  refine le_trans ?_ hov
  have hcard2 : (c / (T : ℝ)) * ((1 / 2 : ℝ) * (T : ℝ))
      ≤ (c / (T : ℝ)) * ((commonValueWindow T).card : ℝ) := by
    apply mul_le_mul_of_nonneg_left hcard
    positivity
  have hsimp : (c / (T : ℝ)) * ((1 / 2 : ℝ) * (T : ℝ)) = c / 2 := by
    field_simp
  rw [hsimp] at hcard2
  exact hcard2


/-! ## Brick 8 — lift to the first-entrance overlap (this is L4). -/

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Topology BigOperators
set_option maxHeartbeats 800000 in
theorem solution (A : ℕ → ℕ) (hA : Tendsto A atTop atTop) :
    ∃ β : ℝ, 0 < β ∧
      ∀ᶠ R in atTop, ∀ x y, rnk x = R + A R → rnk y = R + A R →
        β ≤ ∑ z ∈ (ceilBand R (A R)).filter (fun z => R ≤ rnk z),
              min (enterBandKer Pker (ceilBand R (A R)) x z)
                  (enterBandKer Pker (ceilBand R (A R)) y z) := by
  obtain ⟨β, hβpos, hβev⟩ := Pker_same_ceiling_oneStep_overlap A hA
  refine ⟨β, hβpos, ?_⟩
  filter_upwards [hβev] with R hβR
  intro x y hx hy
  set B := ceilBand R (A R) with hBdef
  set slice := B.filter (fun z => R ≤ rnk z) with hslicedef
  -- x, y are off the band (rank = R + A R, band is {rnk < R + A R})
  have hxB : x ∉ B := by rw [hBdef, mem_ceilBand_iff]; omega
  have hyB : y ∉ B := by rw [hBdef, mem_ceilBand_iff]; omega
  -- in-band slice targets z satisfy z ∈ B, z < x, z < y (rnk z < rnk x = rnk y ⟹ z < x via rnk_mono)
  have hsliceH : ∀ z ∈ slice, z ∈ B ∧ z < x ∧ z < y := by
    intro z hz
    rw [hslicedef, Finset.mem_filter] at hz
    obtain ⟨hzB, _hzR⟩ := hz
    have hzrnk : rnk z < R + A R := mem_ceilBand_iff.mp hzB
    refine ⟨hzB, ?_, ?_⟩
    · -- z < x : else rnk x ≤ rnk z < R+A R = rnk x, contradiction
      by_contra hxz
      push_neg at hxz
      have : rnk x ≤ rnk z := rnk_mono hxz
      omega
    · by_contra hyz
      push_neg at hyz
      have : rnk y ≤ rnk z := rnk_mono hyz
      omega
  have hlift := min_Pker_le_min_enterBandKer_sum (B := B) (slice := slice)
    (x := x) (y := y) hxB hyB hsliceH
  exact le_trans (hβR x y hx hy) hlift
