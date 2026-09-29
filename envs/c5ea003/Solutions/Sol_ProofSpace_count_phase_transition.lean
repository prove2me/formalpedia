-- Prove2me | solution 1 for ProofSpace.count_phase_transition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:56:27.291907+00:00
-- url     : https://prove2.me/submissions/b18db6ca-036c-4bbe-98f3-400444ac0516

-- Sol generated from Logic/ProofSpaceTransition.lean
import Mathlib
import Definitions.Def_Logic_ProofSpaceTransition
import Theorems.Thm_ProofSpace_exists_first_threshold
import Theorems.Thm_ProofSpace_orderParameter_gt_half_iff

/-!
# A discrete Gödel threshold in finite proof space

This file gives a precise finite model of the proposed phase-transition picture.
At cutoff `n`, `provable n` and `unprovable n` count the two classes of statements
seen so far.  Their difference is the signed order parameter.  The main theorem
shows that, whenever this difference starts positive and ends nonpositive, there
is a unique first cutoff at which the provable majority disappears.  Under a
strict-decrease hypothesis, the sign change is permanent and its location is
unique.

This is deliberately a theorem about an abstract enumeration: incompleteness
alone does not imply any particular asymptotic density or power law without a
choice of syntax, length function, and probability measure.
-/

open ProofSpace





/-- The first threshold is unique, without any monotonicity assumption. -/
theorem first_threshold_unique (f : ℕ → ℤ) {a b : ℕ}
    (ha : IsFirstThreshold f a) (hb : IsFirstThreshold f b) : a = b := by
  apply Nat.le_antisymm
  · by_contra h
    push_neg at h
    have : 0 < f b := ha.2 b h
    linarith [hb.1]
  · by_contra h
    push_neg at h
    have : 0 < f a := hb.2 a h
    linarith [ha.1]



/-- A nonpositive imbalance is exactly an order parameter at most one half. -/
theorem orderParameter_le_half_iff {p u : ℕ} (htotal : 0 < p + u) :
    orderParameter p u ≤ (1 / 2 : ℚ) ↔ p ≤ u := by
  simp [orderParameter]
  have hpou : (0 : ℚ) < p + u := by norm_cast
  rw [div_le_iff₀ hpou]
  have h2 : (2 : ℚ)⁻¹ = 1 / 2 := by norm_num
  rw [h2]
  have : (↑p : ℚ) ≤ 1 / 2 * (↑p + ↑u) ↔ 2 * p ≤ p + u := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0 : ℚ) < 2)]
    constructor <;> intro h <;> norm_cast at * <;> ring_nf at * <;> linarith
  rw [this]
  omega





open ProofSpace in
theorem solution(provable unprovable : ℕ → ℕ) (N : ℕ)
    (hpositive : ∀ n ≤ N, 0 < provable n + unprovable n)
    (hdec : ∀ n < N,
      imbalance (provable (n + 1)) (unprovable (n + 1)) <
        imbalance (provable n) (unprovable n))
    (hend : provable N ≤ unprovable N) :
    ∃! n, n ≤ N ∧
      orderParameter (provable n) (unprovable n) ≤ (1 / 2 : ℚ) ∧
      (∀ m < n, (1 / 2 : ℚ) < orderParameter (provable m) (unprovable m)) ∧
      ∀ m, n < m → m ≤ N →
        orderParameter (provable m) (unprovable m) < (1 / 2 : ℚ) := by
  -- Define the imbalance function
  let f := fun n => imbalance (provable n) (unprovable n)
  -- Get the first threshold
  have hN : f N ≤ 0 := by unfold f; simp [imbalance]; omega
  obtain ⟨n, hn_le, hn_first⟩ := exists_first_threshold f N hN
  use n
  refine ⟨⟨hn_le, ?_, ?_, ?_⟩, ?_⟩
  -- Case 1: orderParameter n ≤ 1/2
  · rw [orderParameter_le_half_iff (hpositive n hn_le)]
    have := hn_first.1
    unfold f at this
    simp [imbalance] at this
    linarith
  -- Case 2: For all m < n, orderParameter m > 1/2
  · intro m hm
    rw [orderParameter_gt_half_iff (hpositive m (by linarith))]
    have := hn_first.2 m hm
    unfold f at this
    simp [imbalance] at this
    omega
  -- Case 3: For all m with n < m ≤ N, orderParameter m < 1/2
  · -- First establish orderParameter < 1/2 ↔ p < u
    have ord_lt_half : ∀ p u : ℕ, (0 < p + u) → (orderParameter p u < 1/2 ↔ p < u) := by
      intro p u htotal
      constructor
      · intro h
        by_contra hc
        push_neg at hc
        -- hc : u ≤ p
        -- Need to show orderParameter p u ≥ 1/2 to contradict h : orderParameter p u < 1/2
        have hge : orderParameter p u ≥ 1/2 := by
          have hpu : p ≥ u := hc
          by_contra hc2
          push_neg at hc2
          -- hc2 : orderParameter p u < 1/2
          -- Need to derive a contradiction from p ≥ u
          have hlt : p < u := by
            rw [orderParameter] at hc2
            have hpou : (0 : ℚ) < p + u := by norm_cast
            rw [div_lt_iff₀ hpou] at hc2
            have : (p : ℚ) < u := by linarith
            exact_mod_cast this
          linarith
        linarith
      · intro h
        rw [orderParameter]
        have hpou : (0 : ℚ) < p + u := by norm_cast
        rw [div_lt_iff₀ hpou]
        have : (p : ℚ) < u := by norm_cast
        linarith
    intro m hm1 hm2
    have := (ord_lt_half (provable m) (unprovable m)) (hpositive m hm2)
    rw [this]
    -- Now show provable m < unprovable m using strict decrease
    have hfdec : ∀ k, n < k → k ≤ N → f k < f n := by
      intro k hk1 hk2
      induction k with
      | zero => omega
      | succ k ih =>
        by_cases hk3 : n < k
        · have := ih hk3 (by linarith)
          have := hdec k (by linarith)
          linarith
        · push_neg at hk3
          have : k = n := by omega
          rw [this]
          exact hdec n (by omega)
    have hfm := hfdec m hm1 hm2
    have hfn : f n ≤ 0 := hn_first.1
    simp only [f, imbalance] at hfm hfn
    linarith
  -- Case 4: Uniqueness
  · intro y hy
    obtain ⟨hy_le, hy_le_half, hy_gt_half, _⟩ := hy
    -- y is a first threshold: f y ≤ 0 and ∀ m < y, f m > 0
    have hy_first : IsFirstThreshold f y := by
      constructor
      · -- f y ≤ 0 from hy_le_half
        rw [orderParameter_le_half_iff (hpositive y hy_le)] at hy_le_half
        simp only [f, imbalance]
        omega
      · -- ∀ m < y, f m > 0 from hy_gt_half
        intro m hm
        have := hy_gt_half m hm
        rw [orderParameter_gt_half_iff (hpositive m (by linarith))] at this
        simp only [f, imbalance]
        omega
    exact first_threshold_unique f hy_first hn_first
