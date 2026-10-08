-- Prove2me | solution 1 for ConvexOptimization.two_phase_iteration_count_of_suboptimality
-- status  : ACCEPTED   (prove)
-- author  : @Yifan Hong
-- created : 2026-08-15T08:30:36.215176+00:00
-- url     : https://prove2.me/submissions/1e65aa55-ff22-45a8-a845-946b99d566aa

import Mathlib

private lemma geometric_le_of_loglog_le
    (ε₀ ε : ℝ) (j : ℕ) (hε₀ : 0 < ε₀) (hε : 0 < ε)
    (hεsmall : ε ≤ ε₀ / 4)
    (hj : Real.logb 2 (Real.logb 2 (ε₀ / ε)) ≤ (j : ℝ)) :
    ε₀ * (1 / 2 : ℝ) ^ (2 ^ j) ≤ ε := by
  have hratio_pos : 0 < ε₀ / ε := div_pos hε₀ hε
  have hratio_four : (4 : ℝ) ≤ ε₀ / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hratio_one : (1 : ℝ) < ε₀ / ε := lt_of_lt_of_le (by norm_num) hratio_four
  have hlog_pos : 0 < Real.logb 2 (ε₀ / ε) :=
    Real.logb_pos (by norm_num) hratio_one
  have hinner_le : Real.logb 2 (ε₀ / ε) ≤ (2 : ℝ) ^ (j : ℝ) :=
    (Real.logb_le_iff_le_rpow (by norm_num) hlog_pos).1 hj
  have hratio_le : ε₀ / ε ≤ (2 : ℝ) ^ ((2 : ℝ) ^ (j : ℝ)) :=
    (Real.logb_le_iff_le_rpow (by norm_num) hratio_pos).1 hinner_le
  have hinner_eq : (2 : ℝ) ^ (j : ℝ) = ((2 ^ j : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]
    norm_cast
  have hpow_eq : (2 : ℝ) ^ ((2 : ℝ) ^ (j : ℝ)) = (2 : ℝ) ^ (2 ^ j) := by
    rw [hinner_eq, Real.rpow_natCast]
  rw [hpow_eq] at hratio_le
  have hden_pos : 0 < (2 : ℝ) ^ (2 ^ j) := pow_pos (by norm_num) _
  have hmul : ε₀ ≤ ε * (2 : ℝ) ^ (2 ^ j) := by
    have := (div_le_iff₀ hε).1 hratio_le
    simpa [mul_comm] using this
  rw [show (1 / 2 : ℝ) ^ (2 ^ j) = 1 / (2 : ℝ) ^ (2 ^ j) by
    rw [div_pow]
    simp]
  simpa [div_eq_mul_inv] using
    ((div_le_iff₀ hden_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul))

/-- The discrete counting argument behind the damped and quadratic phases of
Newton's method.  `gap` is the objective gap and `measure` is the quantity
used to detect entry into the quadratic phase. -/
private theorem two_phase_iteration_count
    (gap measure : ℕ → ℝ) (decrease scale threshold ε₀ ε : ℝ)
    (hdecrease : 0 < decrease) (hscale : 0 < scale)
    (hthreshold : 0 < threshold) (hε₀ : 0 < ε₀) (hε : 0 < ε)
    (hεsmall : ε ≤ ε₀ / 4)
    (hscaledThreshold : scale * threshold ≤ 1 / 2)
    (hgap_nonneg : ∀ k, 0 ≤ gap k)
    (hmeasure_nonneg : ∀ k, 0 ≤ measure k)
    (hdamped : ∀ k, threshold ≤ measure k →
      gap (k + 1) ≤ gap k - decrease)
    (hquadratic : ∀ k, measure k < threshold →
      scale * measure (k + 1) ≤ (scale * measure k) ^ 2)
    (hgap_measure : ∀ k, gap k ≤ ε₀ * (scale * measure k) ^ 2)
    (K : ℕ)
    (hK : gap 0 / decrease +
      Real.logb 2 (Real.logb 2 (ε₀ / ε)) ≤ (K : ℝ)) :
    gap K ≤ ε := by
  have hratio_pos : 0 < ε₀ / ε := div_pos hε₀ hε
  have hratio_four : (4 : ℝ) ≤ ε₀ / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hratio_two : (2 : ℝ) < ε₀ / ε := lt_of_lt_of_le (by norm_num) hratio_four
  have hinner_one : (1 : ℝ) < Real.logb 2 (ε₀ / ε) := by
    rw [← Real.logb_self_eq_one (b := (2 : ℝ)) (by norm_num)]
    exact Real.logb_lt_logb (by norm_num) (by norm_num) hratio_two
  have hloglog_pos : 0 < Real.logb 2 (Real.logb 2 (ε₀ / ε)) :=
    Real.logb_pos (by norm_num) hinner_one

  have hgap_before : ∀ q : ℕ,
      (∀ k < q, threshold ≤ measure k) →
        gap q ≤ gap 0 - (q : ℝ) * decrease := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
        intro hbefore
        have hi := ih (fun k hk => hbefore k (Nat.lt_succ_of_lt hk))
        have hd := hdamped q (hbefore q (Nat.lt_succ_self q))
        norm_num [Nat.cast_succ]
        nlinarith

  have hexit : ∃ s : ℕ, s ≤ K ∧ measure s < threshold := by
    by_contra hno
    push Not at hno
    have hbeforeK : ∀ k < K, threshold ≤ measure k := by
      intro k hk
      exact hno k (Nat.le_of_lt hk)
    have hgapK := hgap_before K hbeforeK
    have hK_le : (K : ℝ) ≤ gap 0 / decrease := by
      rw [le_div_iff₀ hdecrease]
      nlinarith [hgap_nonneg K]
    nlinarith

  let s : ℕ := Nat.find hexit
  have hs_spec : s ≤ K ∧ measure s < threshold := Nat.find_spec hexit
  have hsK : s ≤ K := hs_spec.1
  have hs_phase : measure s < threshold := hs_spec.2
  have hmeasure_before_s : ∀ k < s, threshold ≤ measure k := by
    intro k hk
    apply le_of_not_gt
    intro hkphase
    exact Nat.find_min hexit hk ⟨le_trans (Nat.le_of_lt hk) hsK, hkphase⟩
  have hgap_s := hgap_before s hmeasure_before_s
  have hs_le : (s : ℝ) ≤ gap 0 / decrease := by
    rw [le_div_iff₀ hdecrease]
    nlinarith [hgap_nonneg s]

  have hpure : ∀ j : ℕ,
      measure (s + j) < threshold ∧
        scale * measure (s + j) ≤ (1 / 2 : ℝ) ^ (2 ^ j) := by
    intro j
    induction j with
    | zero =>
        constructor
        · simpa using hs_phase
        · have hscaled : scale * measure s < scale * threshold :=
            mul_lt_mul_of_pos_left hs_phase hscale
          simpa using hscaled.le.trans hscaledThreshold
    | succ j ih =>
        have hrec := hquadratic (s + j) ih.1
        have hq_nonneg : 0 ≤ scale * measure (s + j) :=
          mul_nonneg hscale.le (hmeasure_nonneg (s + j))
        have ha_pos : 0 < scale * threshold := mul_pos hscale hthreshold
        have ha_lt_one : scale * threshold < 1 :=
          lt_of_le_of_lt hscaledThreshold (by norm_num)
        have hq_lt_a : scale * measure (s + j) < scale * threshold :=
          mul_lt_mul_of_pos_left ih.1 hscale
        have hsq_lt_a : (scale * measure (s + j)) ^ 2 < scale * threshold := by
          have hsq_lt_sq : (scale * measure (s + j)) ^ 2 <
              (scale * threshold) ^ 2 :=
            (sq_lt_sq₀ hq_nonneg ha_pos.le).2 hq_lt_a
          have haa : (scale * threshold) ^ 2 < scale * threshold := by
            nlinarith
          exact hsq_lt_sq.trans haa
        have hnext_phase : measure (s + (j + 1)) < threshold := by
          have hscaled_next : scale * measure ((s + j) + 1) < scale * threshold :=
            hrec.trans_lt hsq_lt_a
          rw [Nat.add_assoc] at hscaled_next
          exact lt_of_mul_lt_mul_left hscaled_next hscale.le
        constructor
        · simpa [Nat.add_assoc] using hnext_phase
        · have hbound_nonneg : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ j) := by positivity
          have hsq_bound : (scale * measure (s + j)) ^ 2 ≤
              ((1 / 2 : ℝ) ^ (2 ^ j)) ^ 2 :=
            (sq_le_sq₀ hq_nonneg hbound_nonneg).2 ih.2
          have hpow : ((1 / 2 : ℝ) ^ (2 ^ j)) ^ 2 =
              (1 / 2 : ℝ) ^ (2 ^ (j + 1)) := by
            rw [← pow_mul]
            congr 1
          have htrans := hrec.trans hsq_bound
          rw [hpow] at htrans
          simpa [Nat.add_assoc] using htrans

  let j : ℕ := K - s
  have hs_add_j : s + j = K := Nat.add_sub_of_le hsK
  have hj_log : Real.logb 2 (Real.logb 2 (ε₀ / ε)) ≤ (j : ℝ) := by
    dsimp [j]
    rw [Nat.cast_sub hsK]
    linarith
  have hj_pure := hpure j
  rw [hs_add_j] at hj_pure
  have hgeom : ε₀ * (1 / 2 : ℝ) ^ (2 ^ j) ≤ ε :=
    geometric_le_of_loglog_le ε₀ ε j hε₀ hε hεsmall hj_log
  have hq_nonneg : 0 ≤ scale * measure K :=
    mul_nonneg hscale.le (hmeasure_nonneg K)
  have hbound_nonneg : 0 ≤ (1 / 2 : ℝ) ^ (2 ^ j) := by positivity
  have hbound_le_one : (1 / 2 : ℝ) ^ (2 ^ j) ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hq_sq : (scale * measure K) ^ 2 ≤ (1 / 2 : ℝ) ^ (2 ^ j) := by
    nlinarith [hj_pure.2]
  calc
    gap K ≤ ε₀ * (scale * measure K) ^ 2 := hgap_measure K
    _ ≤ ε₀ * (1 / 2 : ℝ) ^ (2 ^ j) := mul_le_mul_of_nonneg_left hq_sq hε₀.le
    _ ≤ ε := hgeom

/-- A formulation of `two_phase_iteration_count` with the usual strong-convexity
suboptimality estimate `gap ≤ measure² / (2m)` exposed explicitly.  The single
normalization identity is exactly what relates the Newton decrement scale to
the reference accuracy `ε₀`. -/
theorem solution
    (gap measure : ℕ → ℝ) (m decrease scale threshold ε₀ ε : ℝ)
    (hm : 0 < m) (hdecrease : 0 < decrease) (hscale : 0 < scale)
    (hthreshold : 0 < threshold) (hε₀ : 0 < ε₀) (hε : 0 < ε)
    (hεsmall : ε ≤ ε₀ / 4)
    (hnormalization : ε₀ * scale ^ 2 = 1 / (2 * m))
    (hscaledThreshold : scale * threshold ≤ 1 / 2)
    (hgap_nonneg : ∀ k, 0 ≤ gap k)
    (hmeasure_nonneg : ∀ k, 0 ≤ measure k)
    (hdamped : ∀ k, threshold ≤ measure k →
      gap (k + 1) ≤ gap k - decrease)
    (hquadratic : ∀ k, measure k < threshold →
      scale * measure (k + 1) ≤ (scale * measure k) ^ 2)
    (hsuboptimality : ∀ k, gap k ≤ measure k ^ 2 / (2 * m))
    (K : ℕ)
    (hK : gap 0 / decrease +
      Real.logb 2 (Real.logb 2 (ε₀ / ε)) ≤ (K : ℝ)) :
    gap K ≤ ε := by
  apply two_phase_iteration_count gap measure decrease scale threshold ε₀ ε
      hdecrease hscale hthreshold hε₀ hε hεsmall hscaledThreshold
      hgap_nonneg hmeasure_nonneg hdamped hquadratic
  · intro k
    refine (hsuboptimality k).trans_eq ?_
    calc
      measure k ^ 2 / (2 * m) = (1 / (2 * m)) * measure k ^ 2 := by ring
      _ = (ε₀ * scale ^ 2) * measure k ^ 2 := by rw [hnormalization]
      _ = ε₀ * (scale * measure k) ^ 2 := by ring
  · exact hK

