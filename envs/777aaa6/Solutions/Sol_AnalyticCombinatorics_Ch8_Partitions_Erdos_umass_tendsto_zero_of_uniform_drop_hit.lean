-- Prove2me | solution 1 for AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_tendsto_zero_of_uniform_drop_hit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:50:52.959777+00:00
-- url     : https://prove2.me/submissions/be811356-a9f4-463d-bb3a-3b52c51b983a

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_FKHittingBridge
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_FKPartitionHitting
import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_KhatRes
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
section
/-!
# R7 Fact B via Doeblin: the deterministic windowed-coupling ITER (finite-sum algebra)

The renewal-alignment overlap bound, built WITHOUT any probabilistic coupling library — purely as
finite-sum recursion over a finite state type `α` with a stochastic kernel `P`.  We track the coalesced
common-minorant mass `ρ_t` and the unmatched pair mass `U_t`; the marginal invariant
`ρ_t z + ∑_y U_t z y = Pⁿ i z` makes `ρ_t` a common minorant of the two `t`-step laws, so
`∑ ρ_t ≤ overlap`.  The unmatched mass contracts: `u_{t+1} ≤ (1−δ) u_t + δ b_t` with `b_t` the unmatched
mass outside the rank window.  Hence

  `overlap(Pᵐ i ·, Pᵐ j ·) ≥ 1 − (1−δ)^m − δ·∑_{t<m} (1−δ)^{m−t−1} b_t`.

The lone analytic input left is the bad-mass bound `b_t ≤ e_t`.  Opus-authored (construction ChatGPT R3).
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]

variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn in
lemma Cpart_nonneg (x y z : α) : 0 ≤ Cpart P rnk W x y z := by
  unfold Cpart; split
  · exact le_min (hPnn x z) (hPnn y z)
  · exact le_refl 0

include hPnn in
lemma Cpart_le_left (x y z : α) : Cpart P rnk W x y z ≤ P x z := by
  unfold Cpart; split
  · exact min_le_left _ _
  · exact hPnn x z

include hPnn in
lemma Cpart_le_right (x y z : α) : Cpart P rnk W x y z ≤ P y z := by
  unfold Cpart; split
  · exact min_le_right _ _
  · exact hPnn y z

include hPnn in
lemma Lres_nonneg (x y z : α) : 0 ≤ Lres P rnk W x y z := by
  unfold Lres; linarith [Cpart_le_left P rnk W hPnn x y z]

include hPnn in
lemma Rres_nonneg (x y z : α) : 0 ≤ Rres P rnk W x y z := by
  unfold Rres; linarith [Cpart_le_right P rnk W hPnn x y z]

include hPnn hPmass in
lemma cmass_le_one (x y : α) : cmass P rnk W x y ≤ 1 := by
  unfold cmass
  calc ∑ z, Cpart P rnk W x y z ≤ ∑ z, P x z :=
        Finset.sum_le_sum (fun z _ => Cpart_le_left P rnk W hPnn x y z)
    _ = 1 := hPmass x

include hPnn in
lemma cmass_nonneg (x y : α) : 0 ≤ cmass P rnk W x y :=
  Finset.sum_nonneg (fun z _ => Cpart_nonneg P rnk W hPnn x y z)

include hPmass in
lemma Lres_sum (x y : α) : ∑ z, Lres P rnk W x y z = 1 - cmass P rnk W x y := by
  unfold Lres cmass
  rw [Finset.sum_sub_distrib, hPmass x]

include hPmass in
lemma Rres_sum (x y : α) : ∑ z, Rres P rnk W x y z = 1 - cmass P rnk W x y := by
  unfold Rres cmass
  rw [Finset.sum_sub_distrib, hPmass y]

include hPnn hPmass in
lemma Kres_nonneg (x y a b : α) : 0 ≤ Kres P rnk W x y a b := by
  unfold Kres; split
  · rename_i h
    exact div_nonneg (mul_nonneg (Lres_nonneg P rnk W hPnn x y a) (Rres_nonneg P rnk W hPnn x y b))
      (by linarith)
  · exact le_refl 0

include hPnn hPmass in
lemma Kres_left_marginal (x y a : α) : ∑ b, Kres P rnk W x y a b = Lres P rnk W x y a := by
  unfold Kres
  by_cases h : cmass P rnk W x y < 1
  · simp only [if_pos h]
    have hne : (1 - cmass P rnk W x y) ≠ 0 := by linarith
    rw [← Finset.sum_div, ← Finset.mul_sum, Rres_sum P rnk W hPmass,
      mul_div_assoc, div_self hne, mul_one]
  · simp only [if_neg h, Finset.sum_const_zero]
    have hc1 : cmass P rnk W x y = 1 := le_antisymm (cmass_le_one P rnk W hPnn hPmass x y) (not_lt.mp h)
    have hL0 : ∑ z, Lres P rnk W x y z = 0 := by rw [Lres_sum P rnk W hPmass, hc1]; ring
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => Lres_nonneg P rnk W hPnn x y z)).mp hL0
    exact (this a (Finset.mem_univ a)).symm

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Conditioned residual kernel

`Kres` is the substochastic residual product kernel whose row mass is `1 - cmass`.
This file normalizes it to a stochastic conditioned-residual kernel.  Rows with
`cmass = 1` are parked at the current pair; the analytic application only uses
the `cmass < 1` rows, but the parked rows make the pair kernel stochastic
globally.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

/-- Point mass at a pair. -/
def pairDelta (i j : α) : α × α → ℝ :=
  fun xy => if xy = (i, j) then 1 else 0

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn hPmass in
lemma Kres_sum (x y : α) :
    ∑ a, ∑ b, Kres P rnk W x y a b = 1 - cmass P rnk W x y := by
  calc
    ∑ a, ∑ b, Kres P rnk W x y a b
        = ∑ a, Lres P rnk W x y a := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          exact Kres_left_marginal P rnk W hPnn hPmass x y a
    _ = 1 - cmass P rnk W x y := Lres_sum P rnk W hPmass x y

include hPnn hPmass in
lemma KhatRes_nonneg (x y a b : α) :
    0 ≤ KhatRes P rnk W x y a b := by
  unfold KhatRes
  by_cases h : cmass P rnk W x y < 1
  · simp only [if_pos h]
    exact div_nonneg (Kres_nonneg P rnk W hPnn hPmass x y a b) (by linarith)
  · simp only [if_neg h]
    split <;> norm_num

include hPnn hPmass in
lemma KhatRes_sum_of_cmass_lt {x y : α} (h : cmass P rnk W x y < 1) :
    ∑ a, ∑ b, KhatRes P rnk W x y a b = 1 := by
  have hden : 1 - cmass P rnk W x y ≠ 0 := by linarith
  unfold KhatRes
  simp only [if_pos h]
  simp_rw [← Finset.sum_div]
  rw [Kres_sum P rnk W hPnn hPmass x y, div_self hden]

include hPnn hPmass in
lemma KhatRes_sum (x y : α) :
    ∑ a, ∑ b, KhatRes P rnk W x y a b = 1 := by
  by_cases h : cmass P rnk W x y < 1
  · exact KhatRes_sum_of_cmass_lt P rnk W hPnn hPmass h
  · unfold KhatRes
    simp only [if_neg h]
    have hinner :
        ∀ a : α, (∑ b : α, if a = x ∧ b = y then (1 : ℝ) else 0) =
          if a = x then 1 else 0 := by
      intro a
      by_cases ha : a = x
      · subst a
        simp
      · simp [ha]
    simp_rw [hinner]
    simp

include hPnn hPmass in
lemma KhatResPair_nonneg (xy zw : α × α) :
    0 ≤ KhatResPair P rnk W xy zw := by
  exact KhatRes_nonneg P rnk W hPnn hPmass xy.1 xy.2 zw.1 zw.2

include hPnn hPmass in
lemma KhatResPair_sum (xy : α × α) :
    ∑ zw, KhatResPair P rnk W xy zw = 1 := by
  cases xy with
  | mk x y =>
      rw [Fintype.sum_prod_type]
      simpa [KhatResPair] using KhatRes_sum P rnk W hPnn hPmass x y

lemma pairDelta_nonneg (i j : α) (xy : α × α) :
    0 ≤ pairDelta i j xy := by
  unfold pairDelta
  split <;> norm_num

lemma pairDelta_sum (i j : α) :
    ∑ xy, pairDelta i j xy = 1 := by
  simp [pairDelta]

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Abstract finite-state Feynman--Kac block bridge

This file contains only finite-sum semigroup algebra.  A stochastic kernel `Q`
with survival weight `w` induces the substochastic kernel
`weightedKernel Q w s z = w s * Q s z`.  If every `M`-step Feynman--Kac block
has a uniform drop, then the total surviving mass tends to zero.
-/

noncomputable section

open Filter Finset Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {S : Type*} [Fintype S]

/-- One step of a substochastic kernel applied to a row vector. -/
def evolve (K : S → S → ℝ) (μ : S → ℝ) : ℕ → S → ℝ
  | 0 => μ
  | t + 1 => fun z => ∑ s, evolve K μ t s * K s z

/-- Total mass after evolving by `K`. -/
def uMass (K : S → S → ℝ) (μ : S → ℝ) (t : ℕ) : ℝ :=
  ∑ s, evolve K μ t s

/-- The `M`-step Feynman--Kac block weight from `s`. -/
def blockWeight (K : S → S → ℝ) : ℕ → S → ℝ
  | 0 => fun _ => 1
  | M + 1 => fun s => ∑ z, K s z * blockWeight K M z

/-- The substochastic kernel with departure-state survival weight `w`. -/
def weightedKernel (Q : S → S → ℝ) (w : S → ℝ) : S → S → ℝ :=
  fun s z => w s * Q s z

lemma evolve_nonneg {K : S → S → ℝ} {μ : S → ℝ}
    (hKnn : ∀ s z, 0 ≤ K s z) (hμnn : ∀ s, 0 ≤ μ s) :
    ∀ t s, 0 ≤ evolve K μ t s := by
  intro t
  induction t with
  | zero =>
      intro s
      exact hμnn s
  | succ t ih =>
      intro z
      simp only [evolve]
      exact Finset.sum_nonneg fun s _ => mul_nonneg (ih s) (hKnn s z)

lemma uMass_nonneg {K : S → S → ℝ} {μ : S → ℝ}
    (hKnn : ∀ s z, 0 ≤ K s z) (hμnn : ∀ s, 0 ≤ μ s) (t : ℕ) :
    0 ≤ uMass K μ t := by
  exact Finset.sum_nonneg fun s _ => evolve_nonneg hKnn hμnn t s

lemma blockWeight_nonneg {K : S → S → ℝ} (hKnn : ∀ s z, 0 ≤ K s z) :
    ∀ M s, 0 ≤ blockWeight K M s := by
  intro M
  induction M with
  | zero =>
      intro s
      simp [blockWeight]
  | succ M ih =>
      intro s
      simp only [blockWeight]
      exact Finset.sum_nonneg fun z _ => mul_nonneg (hKnn s z) (ih z)

lemma blockWeight_nonneg' {K : S → S → ℝ} (hKnn : ∀ s z, 0 ≤ K s z) (M : ℕ) (s : S) :
    0 ≤ blockWeight K M s := by
  exact blockWeight_nonneg hKnn M s

lemma uMass_zero (K : S → S → ℝ) (μ : S → ℝ) :
    uMass K μ 0 = ∑ s, μ s := by
  rfl

lemma uMass_succ (K : S → S → ℝ) (μ : S → ℝ) (t : ℕ) :
    uMass K μ (t + 1) = ∑ s, evolve K μ t s * ∑ z, K s z := by
  unfold uMass
  simp only [evolve]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro s _hs
  rw [Finset.mul_sum]

lemma blockWeight_zero (K : S → S → ℝ) (s : S) :
    blockWeight K 0 s = 1 := by
  rfl

lemma blockWeight_succ (K : S → S → ℝ) (M : ℕ) (s : S) :
    blockWeight K (M + 1) s = ∑ z, K s z * blockWeight K M z := by
  rfl

lemma uMass_add_eq_sum_blockWeight (K : S → S → ℝ) (μ : S → ℝ) :
    ∀ M n, uMass K μ (n + M) = ∑ s, evolve K μ n s * blockWeight K M s := by
  intro M
  induction M with
  | zero =>
      intro n
      simp [blockWeight_zero, uMass]
  | succ M ih =>
      intro n
      rw [show n + (M + 1) = (n + 1) + M by omega]
      rw [ih (n + 1)]
      simp only [evolve, blockWeight_succ]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro s _hs
      calc
        (∑ z, evolve K μ n s * K s z * blockWeight K M z)
            = ∑ z, evolve K μ n s * (K s z * blockWeight K M z) := by
              refine Finset.sum_congr rfl ?_
              intro z _hz
              ring
        _ = evolve K μ n s * ∑ z, K s z * blockWeight K M z := by
              rw [Finset.mul_sum]

lemma exists_pos_of_nonneg_sum_one {μ : S → ℝ} (hμnn : ∀ s, 0 ≤ μ s)
    (hμsum : ∑ s, μ s = 1) :
    ∃ s, 0 < μ s := by
  by_contra h
  have hzero : ∀ s, μ s = 0 := by
    intro s
    exact le_antisymm (le_of_not_gt (fun hs => h ⟨s, hs⟩)) (hμnn s)
  have : ∑ s, μ s = 0 := by simp [hzero]
  linarith

omit [Fintype S] in
lemma weightedKernel_nonneg {Q : S → S → ℝ} {w : S → ℝ}
    (hQnn : ∀ s z, 0 ≤ Q s z) (hw01 : ∀ s, 0 ≤ w s ∧ w s ≤ 1) :
    ∀ s z, 0 ≤ weightedKernel Q w s z := by
  intro s z
  exact mul_nonneg (hw01 s).1 (hQnn s z)

lemma weightedKernel_row_sum {Q : S → S → ℝ} {w : S → ℝ}
    (hQsum : ∀ s, ∑ z, Q s z = 1) (s : S) :
    ∑ z, weightedKernel Q w s z = w s := by
  unfold weightedKernel
  rw [← Finset.mul_sum, hQsum s, mul_one]

lemma weightedKernel_row_le_one {Q : S → S → ℝ} {w : S → ℝ}
    (hQsum : ∀ s, ∑ z, Q s z = 1) (hw01 : ∀ s, 0 ≤ w s ∧ w s ≤ 1) :
    ∀ s, ∑ z, weightedKernel Q w s z ≤ 1 := by
  intro s
  rw [weightedKernel_row_sum hQsum s]
  exact (hw01 s).2

lemma uMass_antitone {K : S → S → ℝ} {μ : S → ℝ}
    (hKnn : ∀ s z, 0 ≤ K s z) (hrow : ∀ s, ∑ z, K s z ≤ 1)
    (hμnn : ∀ s, 0 ≤ μ s) :
    Antitone (uMass K μ) := by
  refine antitone_nat_of_succ_le ?_
  intro t
  rw [uMass_succ]
  have hle : (∑ s, evolve K μ t s * ∑ z, K s z) ≤ ∑ s, evolve K μ t s := by
    refine Finset.sum_le_sum ?_
    intro s _hs
    have hnn := evolve_nonneg hKnn hμnn t s
    calc
      evolve K μ t s * (∑ z, K s z) ≤ evolve K μ t s * 1 :=
        mul_le_mul_of_nonneg_left (hrow s) hnn
      _ = evolve K μ t s := by ring
  exact hle

lemma nat_div_tendsto_atTop {M : ℕ} (hM : 0 < M) :
    Tendsto (fun n : ℕ => n / M) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b * M, fun n hn => ?_⟩
  exact (Nat.le_div_iff_mul_le hM).2 hn

/-- Abstract finite-state FK block bridge.

If every length-`M` block has survival weight at most `1 - c0`, then the total
mass of the substochastic FK semigroup tends to zero. -/
theorem fk_block_bridge
    (Q : S → S → ℝ) (w : S → ℝ)
    (hQnn : ∀ s z, 0 ≤ Q s z) (hQsum : ∀ s, ∑ z, Q s z = 1)
    (hw01 : ∀ s, 0 ≤ w s ∧ w s ≤ 1)
    (M : ℕ) (hM : 0 < M) (c0 : ℝ) (hc0 : 0 < c0)
    (hdrop : ∀ s, blockWeight (weightedKernel Q w) M s ≤ 1 - c0)
    (μ0 : S → ℝ) (hμ0nn : ∀ s, 0 ≤ μ0 s) (hμ0sum : ∑ s, μ0 s = 1) :
    Tendsto (fun t => uMass (weightedKernel Q w) μ0 t) atTop (𝓝 0) := by
  let K := weightedKernel Q w
  let q : ℝ := 1 - c0
  have hKnn : ∀ s z, 0 ≤ K s z := weightedKernel_nonneg hQnn hw01
  have hrow : ∀ s, ∑ z, K s z ≤ 1 := weightedKernel_row_le_one hQsum hw01
  have hanti : Antitone (uMass K μ0) := uMass_antitone hKnn hrow hμ0nn
  have hq_nonneg : 0 ≤ q := by
    obtain ⟨s0, hs0⟩ := exists_pos_of_nonneg_sum_one hμ0nn hμ0sum
    have hbnn : 0 ≤ blockWeight K M s0 := blockWeight_nonneg' hKnn M s0
    have hbd : blockWeight K M s0 ≤ q := hdrop s0
    linarith
  have hq_lt_one : q < 1 := by
    dsimp [q]
    linarith
  have hcontract : ∀ n, uMass K μ0 (n + M) ≤ q * uMass K μ0 n := by
    intro n
    rw [uMass_add_eq_sum_blockWeight K μ0 M n]
    have hle : (∑ s, evolve K μ0 n s * blockWeight K M s) ≤
        ∑ s, evolve K μ0 n s * q := by
      refine Finset.sum_le_sum ?_
      intro s _hs
      exact mul_le_mul_of_nonneg_left (hdrop s) (evolve_nonneg hKnn hμ0nn n s)
    calc
      (∑ s, evolve K μ0 n s * blockWeight K M s)
          ≤ ∑ s, evolve K μ0 n s * q := hle
      _ = q * uMass K μ0 n := by
          unfold uMass
          rw [← Finset.sum_mul]
          ring
  have hblock : ∀ k : ℕ, uMass K μ0 (k * M) ≤ q ^ k := by
    intro k
    induction k with
    | zero =>
        rw [Nat.zero_mul, pow_zero, uMass_zero, hμ0sum]
    | succ k ih =>
        have hc := hcontract (k * M)
        calc
          uMass K μ0 ((k + 1) * M) ≤ q * uMass K μ0 (k * M) := by
            simpa [Nat.succ_mul] using hc
          _ ≤ q * q ^ k := mul_le_mul_of_nonneg_left ih hq_nonneg
          _ = q ^ (k + 1) := by ring
  have hpow : Tendsto (fun k : ℕ => q ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one
  have hpowdiv : Tendsto (fun n : ℕ => q ^ (n / M)) atTop (𝓝 0) :=
    hpow.comp (nat_div_tendsto_atTop hM)
  have hupper : ∀ n : ℕ, uMass K μ0 n ≤ q ^ (n / M) := by
    intro n
    have hle : (n / M) * M ≤ n := Nat.div_mul_le_self n M
    exact (hanti hle).trans (hblock (n / M))
  exact squeeze_zero' (Eventually.of_forall (uMass_nonneg hKnn hμ0nn)) (Eventually.of_forall hupper)
    hpowdiv

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Hitting-to-FK block drop

This file contains the finite-state algebraic corollary used by the concrete
block-drop task: if the free walk hits a drop set with uniformly positive
probability during a block, then the Feynman--Kac block weight has a uniform
drop.
-/

noncomputable section

open Finset

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {S : Type*} [Fintype S]

lemma blockWeight_le_one {K : S → S → ℝ}
    (hKnn : ∀ s z, 0 ≤ K s z) (hrow : ∀ s, ∑ z, K s z ≤ 1) :
    ∀ M s, blockWeight K M s ≤ 1 := by
  intro M
  induction M with
  | zero =>
      intro s
      simp [blockWeight]
  | succ M ih =>
      intro s
      rw [blockWeight_succ]
      calc
        (∑ z, K s z * blockWeight K M z) ≤ ∑ z, K s z * 1 := by
          refine Finset.sum_le_sum ?_
          intro z _hz
          exact mul_le_mul_of_nonneg_left (ih z) (hKnn s z)
        _ = ∑ z, K s z := by simp
        _ ≤ 1 := hrow s

lemma blockWeight_le_one_minus_delta_hitProb
    (Q : S → S → ℝ) (w : S → ℝ) (A : S → Prop) [DecidablePred A] (δ : ℝ)
    (hQnn : ∀ s z, 0 ≤ Q s z) (hQsum : ∀ s, ∑ z, Q s z = 1)
    (hw01 : ∀ s, 0 ≤ w s ∧ w s ≤ 1)
    (hdrop_on_A : ∀ s, A s → w s ≤ 1 - δ) :
    ∀ M s,
      blockWeight (weightedKernel Q w) M s ≤ 1 - δ * hitProb Q A M s := by
  let K := weightedKernel Q w
  have hKnn : ∀ s z, 0 ≤ K s z := weightedKernel_nonneg hQnn hw01
  have hrow : ∀ s, ∑ z, K s z ≤ 1 := weightedKernel_row_le_one hQsum hw01
  intro M
  induction M with
  | zero =>
      intro s
      simp [blockWeight, hitProb]
  | succ M ih =>
      intro s
      rw [blockWeight_succ]
      simp only [hitProb]
      by_cases hs : A s
      · simp only [if_pos hs]
        have hsum_le_one : (∑ z, Q s z * blockWeight K M z) ≤ 1 := by
          calc
            (∑ z, Q s z * blockWeight K M z) ≤ ∑ z, Q s z * 1 := by
              refine Finset.sum_le_sum ?_
              intro z _hz
              exact mul_le_mul_of_nonneg_left (blockWeight_le_one hKnn hrow M z) (hQnn s z)
            _ = ∑ z, Q s z := by simp
            _ = 1 := hQsum s
        have hfactor :
            (∑ z, K s z * blockWeight K M z) =
              w s * ∑ z, Q s z * blockWeight K M z := by
          dsimp [K, weightedKernel]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
        rw [hfactor]
        calc
          w s * (∑ z, Q s z * blockWeight K M z) ≤ w s * 1 :=
            mul_le_mul_of_nonneg_left hsum_le_one (hw01 s).1
          _ = w s := by ring
          _ ≤ 1 - δ := hdrop_on_A s hs
          _ = 1 - δ * 1 := by ring
      · simp only [if_neg hs]
        have hsum_nonneg : 0 ≤ ∑ z, Q s z * blockWeight K M z :=
          Finset.sum_nonneg fun z _ => mul_nonneg (hQnn s z) (blockWeight_nonneg' hKnn M z)
        have hfactor :
            (∑ z, K s z * blockWeight K M z) =
              w s * ∑ z, Q s z * blockWeight K M z := by
          dsimp [K, weightedKernel]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
        have hfree :
            (∑ z, Q s z * blockWeight K M z)
              ≤ ∑ z, Q s z * (1 - δ * hitProb Q A M z) := by
          refine Finset.sum_le_sum ?_
          intro z _hz
          exact mul_le_mul_of_nonneg_left (ih z) (hQnn s z)
        rw [hfactor]
        calc
          w s * (∑ z, Q s z * blockWeight K M z)
              ≤ 1 * (∑ z, Q s z * blockWeight K M z) :=
                mul_le_mul_of_nonneg_right (hw01 s).2 hsum_nonneg
          _ = ∑ z, Q s z * blockWeight K M z := by ring
          _ ≤ ∑ z, Q s z * (1 - δ * hitProb Q A M z) := hfree
          _ = 1 - δ * ∑ z, Q s z * hitProb Q A M z := by
            calc
              (∑ z, Q s z * (1 - δ * hitProb Q A M z))
                  = ∑ z, (Q s z - δ * (Q s z * hitProb Q A M z)) := by
                    refine Finset.sum_congr rfl ?_
                    intro z _hz
                    ring
              _ = (∑ z, Q s z) - δ * ∑ z, Q s z * hitProb Q A M z := by
                    rw [Finset.sum_sub_distrib, Finset.mul_sum]
              _ = 1 - δ * ∑ z, Q s z * hitProb Q A M z := by rw [hQsum s]

/-- A uniform free-walk hitting lower bound gives a uniform FK block drop. -/
theorem blockWeight_le_of_hitProb
    (Q : S → S → ℝ) (w : S → ℝ) (A : S → Prop) [DecidablePred A]
    (δ p0 : ℝ)
    (hQnn : ∀ s z, 0 ≤ Q s z) (hQsum : ∀ s, ∑ z, Q s z = 1)
    (hw01 : ∀ s, 0 ≤ w s ∧ w s ≤ 1)
    (hδ0 : 0 ≤ δ) (hdrop_on_A : ∀ s, A s → w s ≤ 1 - δ)
    (M : ℕ) (hhit : ∀ s, p0 ≤ hitProb Q A M s) :
    ∀ s, blockWeight (weightedKernel Q w) M s ≤ 1 - δ * p0 := by
  intro s
  calc
    blockWeight (weightedKernel Q w) M s ≤ 1 - δ * hitProb Q A M s :=
      blockWeight_le_one_minus_delta_hitProb Q w A δ hQnn hQsum hw01 hdrop_on_A M s
    _ ≤ 1 - δ * p0 := by
      exact sub_le_sub_left (mul_le_mul_of_nonneg_left (hhit s) hδ0) 1

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

section
/-!
# Feynman--Kac bridge for the partition residual coupling

This file instantiates the abstract finite-state FK block bridge for the
partition residual coupling.  The residual kernel factors as the stochastic
conditioned residual kernel `KhatResPair` times the departure survival weight
`1 - cmass`; consequently `umass` is exactly the total mass of the associated
FK semigroup.
-/

noncomputable section

open Filter Finset Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

/-- The residual product coupling kernel as a kernel on pair states. -/
def KresPair (xy zw : α × α) : ℝ :=
  Kres P rnk W xy.1 xy.2 zw.1 zw.2

/-- FK survival weight for a departure pair. -/
def survivalWeight (xy : α × α) : ℝ :=
  1 - cmass P rnk W xy.1 xy.2

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

include hPnn hPmass in
lemma Kres_factor_KhatRes (x y a b : α) :
    Kres P rnk W x y a b =
      (1 - cmass P rnk W x y) * KhatRes P rnk W x y a b := by
  by_cases h : cmass P rnk W x y < 1
  · have hden : 1 - cmass P rnk W x y ≠ 0 := by linarith
    unfold KhatRes
    simp only [if_pos h]
    field_simp [hden]
  · have hc1 : cmass P rnk W x y = 1 :=
      le_antisymm (cmass_le_one P rnk W hPnn hPmass x y) (not_lt.mp h)
    unfold Kres KhatRes
    simp [hc1]

include hPnn hPmass in
lemma KresPair_eq_weightedKernel :
    KresPair P rnk W =
      weightedKernel (KhatResPair P rnk W) (survivalWeight P rnk W) := by
  funext xy zw
  cases xy with
  | mk x y =>
      cases zw with
      | mk a b =>
          simp [KresPair, weightedKernel, KhatResPair, survivalWeight,
            Kres_factor_KhatRes P rnk W hPnn hPmass x y a b]

omit [DecidableEq α] in
include hPnn hPmass in
lemma survivalWeight_01 (xy : α × α) :
    0 ≤ survivalWeight P rnk W xy ∧ survivalWeight P rnk W xy ≤ 1 := by
  classical
  cases xy with
  | mk x y =>
      constructor
      · dsimp [survivalWeight]
        linarith [cmass_le_one P rnk W hPnn hPmass x y]
      · dsimp [survivalWeight]
        linarith [cmass_nonneg P rnk W hPnn x y]

lemma evolve_KresPair_pairDelta_eq_Umat (i j : α) :
    ∀ t xy,
      evolve (KresPair P rnk W) (pairDelta i j) t xy =
        Umat P rnk W i j t xy.1 xy.2 := by
  intro t
  induction t with
  | zero =>
      intro xy
      cases xy with
      | mk a b =>
          simp [evolve, pairDelta, Umat, Prod.ext_iff]
  | succ t ih =>
      intro xy
      cases xy with
      | mk a b =>
          simp only [evolve, Umat]
          rw [Fintype.sum_prod_type]
          refine Finset.sum_congr rfl ?_
          intro x _hx
          refine Finset.sum_congr rfl ?_
          intro y _hy
          rw [ih (x, y)]
          rfl

lemma umass_eq_uMass_KresPair (i j : α) (t : ℕ) :
    umass P rnk W i j t =
      uMass (KresPair P rnk W) (pairDelta i j) t := by
  unfold umass uMass
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  refine Finset.sum_congr rfl ?_
  intro y _hy
  rw [evolve_KresPair_pairDelta_eq_Umat P rnk W i j t (x, y)]

include hPnn hPmass in
/-- `umass` tends to zero from a uniform FK block drop for the concrete residual walk. -/
theorem umass_tendsto_zero_of_fk_block_drop (i j : α)
    (M : ℕ) (hM : 0 < M) (c0 : ℝ) (hc0 : 0 < c0)
    (hdrop :
      ∀ xy, blockWeight
        (weightedKernel (KhatResPair P rnk W) (survivalWeight P rnk W)) M xy ≤ 1 - c0) :
    Tendsto (fun t => umass P rnk W i j t) atTop (𝓝 0) := by
  have hfk := fk_block_bridge
    (Q := KhatResPair P rnk W)
    (w := survivalWeight P rnk W)
    (hQnn := KhatResPair_nonneg P rnk W hPnn hPmass)
    (hQsum := KhatResPair_sum P rnk W hPnn hPmass)
    (hw01 := survivalWeight_01 P rnk W hPnn hPmass)
    (M := M) (hM := hM) (c0 := c0) (hc0 := hc0)
    (hdrop := hdrop)
    (μ0 := pairDelta i j)
    (hμ0nn := pairDelta_nonneg i j)
    (hμ0sum := pairDelta_sum i j)
  refine hfk.congr' ?_
  exact Eventually.of_forall fun t => by
    rw [← KresPair_eq_weightedKernel P rnk W hPnn hPmass]
    change uMass (KresPair P rnk W) (pairDelta i j) t = umass P rnk W i j t
    exact (umass_eq_uMass_KresPair P rnk W i j t).symm

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end
end

/-!
# Partition FK hitting bridge

This file packages the concrete drop-set interface for the partition residual
coupling: a uniform free-`KhatRes` hitting lower bound for
`{xy | δ ≤ cmass xy}` implies `umass → 0`.
-/

noncomputable section

open Filter Topology

namespace AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)

variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)

omit [DecidableEq α] in
lemma survivalWeight_le_of_dropSet (δ : ℝ) (xy : α × α)
    (hxy : dropSet P rnk W δ xy) :
    survivalWeight P rnk W xy ≤ 1 - δ := by
  dsimp [survivalWeight, dropSet] at hxy ⊢
  linarith

end AnalyticCombinatorics.Ch8.Partitions.Erdos
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos
open Filter Topology
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
include hPnn hPmass in
theorem solution (i j : α)
    (δ p0 : ℝ) (hδ : 0 < δ) (hp0 : 0 < p0)
    (M : ℕ) (hM : 0 < M)
    (hhit :
      ∀ xy, p0 ≤ hitProb (KhatResPair P rnk W) (dropSet P rnk W δ) M xy) :
    Tendsto (fun t => umass P rnk W i j t) atTop (𝓝 0) := by
  classical
  have hc0 : 0 < δ * p0 := mul_pos hδ hp0
  have hdrop :
      ∀ xy, blockWeight
        (weightedKernel (KhatResPair P rnk W) (survivalWeight P rnk W)) M xy
          ≤ 1 - δ * p0 :=
    blockWeight_le_of_hitProb
      (Q := KhatResPair P rnk W)
      (w := survivalWeight P rnk W)
      (A := dropSet P rnk W δ)
      (δ := δ) (p0 := p0)
      (hQnn := KhatResPair_nonneg P rnk W hPnn hPmass)
      (hQsum := KhatResPair_sum P rnk W hPnn hPmass)
      (hw01 := survivalWeight_01 P rnk W hPnn hPmass)
      (hδ0 := hδ.le)
      (hdrop_on_A := survivalWeight_le_of_dropSet P rnk W δ)
      (M := M) hhit
  exact umass_tendsto_zero_of_fk_block_drop P rnk W hPnn hPmass i j M hM (δ * p0) hc0 hdrop
