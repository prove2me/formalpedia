-- Prove2me | solution 1 for markov_entanglement_bellman_q_error_of_local_tv
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-07-18T16:19:10.657061+00:00
-- url     : https://prove2.me/submissions/7c1d3f3c-0f6f-4036-95e4-419a8b47342d

import Definitions.Def_markov_entanglement

open scoped BigOperators
open MarkovEntanglement

private theorem bellman_sup_norm
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P : Matrix ι ι ℝ) (hP : IsTransitionMatrix P)
    (r Q : ι → ℝ) (γ rmax : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hr : ∀ i, |r i| ≤ rmax) (hQ : IsBellmanQ P r γ Q) :
    (⨆ i : ι, |Q i|) ≤ rmax / (1 - γ) := by
  classical
  let u : ℝ := ⨆ i : ι, |Q i|
  have hQu (i : ι) : |Q i| ≤ u :=
    le_ciSup (f := fun i : ι => |Q i|) (Finite.bddAbove_range _) i
  have hsum (i : ι) : |∑ j, P i j * Q j| ≤ u := by
    calc
      |∑ j, P i j * Q j| ≤ ∑ j, |P i j * Q j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, P i j * u := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_of_nonneg (hP.1 i j)]
        exact mul_le_mul_of_nonneg_left (hQu j) (hP.1 i j)
      _ = u := by rw [← Finset.sum_mul, hP.2 i, one_mul]
  have hpoint (i : ι) : |Q i| ≤ rmax + γ * u := by
    calc
      |Q i| = |r i + γ * ∑ j, P i j * Q j| := by rw [hQ i]
      _ ≤ |r i| + |γ * ∑ j, P i j * Q j| := abs_add_le _ _
      _ = |r i| + γ * |∑ j, P i j * Q j| := by rw [abs_mul, abs_of_nonneg hγ0]
      _ ≤ rmax + γ * u :=
        add_le_add (hr i) (mul_le_mul_of_nonneg_left (hsum i) hγ0)
  have hu : u ≤ rmax + γ * u := ciSup_le hpoint
  apply (le_div_iff₀ (sub_pos.mpr hγ1)).2
  nlinarith

private theorem tv_action_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (P Q : Matrix ι ι ℝ) (v : ι → ℝ) (i : ι) :
    |∑ j, (P i j - Q i j) * v j| ≤
      2 * tvDist P Q * (⨆ j : ι, |v j|) := by
  classical
  let u : ℝ := ⨆ j : ι, |v j|
  have hv (j : ι) : |v j| ≤ u :=
    le_ciSup (f := fun j : ι => |v j|) (Finite.bddAbove_range _) j
  let i₀ : ι := Classical.choice inferInstance
  have hu : 0 ≤ u := le_trans (abs_nonneg (v i₀)) (hv i₀)
  have hrow : (1 / 2 : ℝ) * ∑ j, |P i j - Q i j| ≤ tvDist P Q := by
    unfold tvDist
    exact le_ciSup (f := fun i : ι => (1 / 2 : ℝ) * ∑ j, |P i j - Q i j|)
      (Finite.bddAbove_range _) i
  have hsum : ∑ j, |P i j - Q i j| ≤ 2 * tvDist P Q := by
    nlinarith
  calc
    |∑ j, (P i j - Q i j) * v j| ≤ ∑ j, |(P i j - Q i j) * v j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |P i j - Q i j| * u := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
    _ = (∑ j, |P i j - Q i j|) * u := by rw [Finset.sum_mul]
    _ ≤ (2 * tvDist P Q) * u := mul_le_mul_of_nonneg_right hsum hu
    _ = 2 * tvDist P Q * u := by ring

private theorem tvDist_comm
    {ι : Type*} [Fintype ι] (P Q : Matrix ι ι ℝ) :
    tvDist P Q = tvDist Q P := by
  classical
  unfold tvDist
  apply iSup_congr
  intro i
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact abs_sub_comm _ _

private theorem agentA_action_bound
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    [Nonempty SA] [Nonempty SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (PA : Matrix SA SA ℝ)
    (v : SA → ℝ) (p : SA × SB) :
    |∑ a : SA, ((∑ b : SB, P p (a, b)) - PA p.1 a) * v a| ≤
      2 * agentTVDistA P PA * (⨆ a : SA, |v a|) := by
  classical
  let u : ℝ := ⨆ a : SA, |v a|
  have hv (a : SA) : |v a| ≤ u :=
    le_ciSup (f := fun a : SA => |v a|) (Finite.bddAbove_range _) a
  let a₀ : SA := Classical.choice inferInstance
  have hu : 0 ≤ u := le_trans (abs_nonneg (v a₀)) (hv a₀)
  have hrow : (1 / 2 : ℝ) * ∑ a : SA, |(∑ b : SB, P p (a, b)) - PA p.1 a| ≤
      agentTVDistA P PA := by
    unfold agentTVDistA
    exact le_ciSup
      (f := fun q : SA × SB =>
        (1 / 2 : ℝ) * ∑ a : SA, |(∑ b : SB, P q (a, b)) - PA q.1 a|)
      (Finite.bddAbove_range _) p
  have hsum : ∑ a : SA, |(∑ b : SB, P p (a, b)) - PA p.1 a| ≤
      2 * agentTVDistA P PA := by
    nlinarith
  calc
    |∑ a : SA, ((∑ b : SB, P p (a, b)) - PA p.1 a) * v a| ≤
        ∑ a : SA, |((∑ b : SB, P p (a, b)) - PA p.1 a) * v a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : SA, |(∑ b : SB, P p (a, b)) - PA p.1 a| * u := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv a) (abs_nonneg _)
    _ = (∑ a : SA, |(∑ b : SB, P p (a, b)) - PA p.1 a|) * u := by
      rw [Finset.sum_mul]
    _ ≤ (2 * agentTVDistA P PA) * u := mul_le_mul_of_nonneg_right hsum hu
    _ = 2 * agentTVDistA P PA * u := by ring

private theorem agentB_action_bound
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    [Nonempty SA] [Nonempty SB]
    (P : Matrix (SA × SB) (SA × SB) ℝ) (PB : Matrix SB SB ℝ)
    (v : SB → ℝ) (p : SA × SB) :
    |∑ b : SB, ((∑ a : SA, P p (a, b)) - PB p.2 b) * v b| ≤
      2 * agentTVDistB P PB * (⨆ b : SB, |v b|) := by
  classical
  let u : ℝ := ⨆ b : SB, |v b|
  have hv (b : SB) : |v b| ≤ u :=
    le_ciSup (f := fun b : SB => |v b|) (Finite.bddAbove_range _) b
  let b₀ : SB := Classical.choice inferInstance
  have hu : 0 ≤ u := le_trans (abs_nonneg (v b₀)) (hv b₀)
  have hrow : (1 / 2 : ℝ) * ∑ b : SB, |(∑ a : SA, P p (a, b)) - PB p.2 b| ≤
      agentTVDistB P PB := by
    unfold agentTVDistB
    exact le_ciSup
      (f := fun q : SA × SB =>
        (1 / 2 : ℝ) * ∑ b : SB, |(∑ a : SA, P q (a, b)) - PB q.2 b|)
      (Finite.bddAbove_range _) p
  have hsum : ∑ b : SB, |(∑ a : SA, P p (a, b)) - PB p.2 b| ≤
      2 * agentTVDistB P PB := by
    nlinarith
  calc
    |∑ b : SB, ((∑ a : SA, P p (a, b)) - PB p.2 b) * v b| ≤
        ∑ b : SB, |((∑ a : SA, P p (a, b)) - PB p.2 b) * v b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : SB, |(∑ a : SA, P p (a, b)) - PB p.2 b| * u := by
      apply Finset.sum_le_sum
      intro b hb
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hv b) (abs_nonneg _)
    _ = (∑ b : SB, |(∑ a : SA, P p (a, b)) - PB p.2 b|) * u := by
      rw [Finset.sum_mul]
    _ ≤ (2 * agentTVDistB P PB) * u := mul_le_mul_of_nonneg_right hsum hu
    _ = 2 * agentTVDistB P PB * u := by ring

theorem solution
    {SA SB : Type*} [Fintype SA] [Fintype SB] [DecidableEq SA] [DecidableEq SB]
    (P_AB : Matrix (SA × SB) (SA × SB) ℝ) (hP_AB : IsTransitionMatrix P_AB)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (r_A : SA → ℝ) (r_B : SB → ℝ) (rAmax rBmax : ℝ)
    (hrAmax : 0 ≤ rAmax) (hrBmax : 0 ≤ rBmax)
    (hrA : ∀ a, |r_A a| ≤ rAmax) (hrB : ∀ b, |r_B b| ≤ rBmax)
    (P_true_A : Matrix SA SA ℝ) (hP_true_A_tm : IsTransitionMatrix P_true_A)
    (P_true_B : Matrix SB SB ℝ) (hP_true_B_tm : IsTransitionMatrix P_true_B)
    (Q_AB : SA × SB → ℝ) (hQ_AB : IsBellmanQ P_AB (fun p => r_A p.1 + r_B p.2) γ Q_AB)
    (Q_true_A : SA → ℝ) (hQ_true_A : IsBellmanQ P_true_A r_A γ Q_true_A)
    (Q_true_B : SB → ℝ) (hQ_true_B : IsBellmanQ P_true_B r_B γ Q_true_B)
    (P_A : Matrix SA SA ℝ) (hP_A_tm : IsTransitionMatrix P_A)
    (hP_A_opt : agentTVDistA P_AB P_A = entanglementA P_AB)
    (P_B : Matrix SB SB ℝ) (hP_B_tm : IsTransitionMatrix P_B)
    (hP_B_opt : agentTVDistB P_AB P_B = entanglementB P_AB)
    (hTVA : tvDist P_true_A P_A ≤ entanglementA P_AB)
    (hTVB : tvDist P_true_B P_B ≤ entanglementB P_AB) :
    (⨆ p : SA × SB, |Q_AB p - (Q_true_A p.1 + Q_true_B p.2)|) ≤
      4 * γ * (entanglementA P_AB * rAmax + entanglementB P_AB * rBmax) / (1 - γ) ^ 2 := by
  classical
  by_cases hp : Nonempty (SA × SB)
  · letI : Nonempty (SA × SB) := hp
    letI : Nonempty SA := ⟨(Classical.choice hp).1⟩
    letI : Nonempty SB := ⟨(Classical.choice hp).2⟩
    let D : SA × SB → ℝ := fun p => Q_AB p - (Q_true_A p.1 + Q_true_B p.2)
    let u : ℝ := ⨆ p : SA × SB, |D p|
    let uA : ℝ := ⨆ a : SA, |Q_true_A a|
    let uB : ℝ := ⨆ b : SB, |Q_true_B b|
    have hDu (p : SA × SB) : |D p| ≤ u :=
      le_ciSup (f := fun p : SA × SB => |D p|) (Finite.bddAbove_range _) p
    have hu0 : 0 ≤ u := by
      let p₀ : SA × SB := Classical.choice hp
      exact le_trans (abs_nonneg (D p₀)) (hDu p₀)
    have hUA : uA ≤ rAmax / (1 - γ) :=
      bellman_sup_norm P_true_A hP_true_A_tm r_A Q_true_A γ rAmax hγ0 hγ1 hrA hQ_true_A
    have hUB : uB ≤ rBmax / (1 - γ) :=
      bellman_sup_norm P_true_B hP_true_B_tm r_B Q_true_B γ rBmax hγ0 hγ1 hrB hQ_true_B
    have huA0 : 0 ≤ uA := by
      let a₀ : SA := Classical.choice inferInstance
      exact le_trans (abs_nonneg (Q_true_A a₀))
        (le_ciSup (f := fun a : SA => |Q_true_A a|) (Finite.bddAbove_range _) a₀)
    have huB0 : 0 ≤ uB := by
      let b₀ : SB := Classical.choice inferInstance
      exact le_trans (abs_nonneg (Q_true_B b₀))
        (le_ciSup (f := fun b : SB => |Q_true_B b|) (Finite.bddAbove_range _) b₀)
    have htvA0 : 0 ≤ tvDist P_true_A P_A := by
      let a₀ : SA := Classical.choice inferInstance
      apply le_trans (b := (1 / 2 : ℝ) * ∑ j : SA, |P_true_A a₀ j - P_A a₀ j|)
      · positivity
      · unfold tvDist
        exact le_ciSup
          (f := fun a : SA => (1 / 2 : ℝ) * ∑ j : SA, |P_true_A a j - P_A a j|)
          (Finite.bddAbove_range _) a₀
    have htvB0 : 0 ≤ tvDist P_true_B P_B := by
      let b₀ : SB := Classical.choice inferInstance
      apply le_trans (b := (1 / 2 : ℝ) * ∑ j : SB, |P_true_B b₀ j - P_B b₀ j|)
      · positivity
      · unfold tvDist
        exact le_ciSup
          (f := fun b : SB => (1 / 2 : ℝ) * ∑ j : SB, |P_true_B b j - P_B b j|)
          (Finite.bddAbove_range _) b₀
    have hEA0 : 0 ≤ entanglementA P_AB := htvA0.trans hTVA
    have hEB0 : 0 ≤ entanglementB P_AB := htvB0.trans hTVB
    have hJoint (p : SA × SB) :
        (∑ q : SA × SB, P_AB p q * Q_AB q) =
          (∑ q : SA × SB, P_AB p q * D q) +
          (∑ a : SA, (∑ b : SB, P_AB p (a, b)) * Q_true_A a) +
          (∑ b : SB, (∑ a : SA, P_AB p (a, b)) * Q_true_B b) := by
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      simp_rw [show ∀ a b, Q_AB (a, b) = D (a, b) + (Q_true_A a + Q_true_B b) by
        intro a b
        dsimp [D]
        ring]
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [show (∑ a : SA, ∑ b : SB, P_AB p (a, b) * Q_true_A a) =
          ∑ a : SA, (∑ b : SB, P_AB p (a, b)) * Q_true_A a by
        simp_rw [Finset.sum_mul]]
      rw [show (∑ a : SA, ∑ b : SB, P_AB p (a, b) * Q_true_B b) =
          ∑ b : SB, (∑ a : SA, P_AB p (a, b)) * Q_true_B b by
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]]
      ring
    have hpoint (p : SA × SB) :
        |D p| ≤ γ * u +
          4 * γ * (entanglementA P_AB * uA + entanglementB P_AB * uB) := by
      let sD := ∑ q : SA × SB, P_AB p q * D q
      let eA₁ := ∑ a : SA, ((∑ b : SB, P_AB p (a, b)) - P_A p.1 a) * Q_true_A a
      let eA₂ := ∑ a : SA, (P_A p.1 a - P_true_A p.1 a) * Q_true_A a
      let eB₁ := ∑ b : SB, ((∑ a : SA, P_AB p (a, b)) - P_B p.2 b) * Q_true_B b
      let eB₂ := ∑ b : SB, (P_B p.2 b - P_true_B p.2 b) * Q_true_B b
      have hDeq : D p = γ * (sD + eA₁ + eA₂ + eB₁ + eB₂) := by
        dsimp [D, sD, eA₁, eA₂, eB₁, eB₂]
        rw [hQ_AB p, hQ_true_A p.1, hQ_true_B p.2, hJoint p]
        simp_rw [sub_mul, Finset.sum_sub_distrib]
        ring
      have hsD : |sD| ≤ u := by
        dsimp [sD]
        calc
          |∑ q : SA × SB, P_AB p q * D q| ≤ ∑ q : SA × SB, |P_AB p q * D q| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ q : SA × SB, P_AB p q * u := by
            apply Finset.sum_le_sum
            intro q hq
            rw [abs_mul, abs_of_nonneg (hP_AB.1 p q)]
            exact mul_le_mul_of_nonneg_left (hDu q) (hP_AB.1 p q)
          _ = u := by rw [← Finset.sum_mul, hP_AB.2 p, one_mul]
      have heA₁ : |eA₁| ≤ 2 * entanglementA P_AB * uA := by
        dsimp [eA₁, uA]
        simpa [hP_A_opt] using agentA_action_bound P_AB P_A Q_true_A p
      have heA₂base : |eA₂| ≤ 2 * tvDist P_A P_true_A * uA := by
        dsimp [eA₂, uA]
        exact tv_action_bound P_A P_true_A Q_true_A p.1
      have heA₂ : |eA₂| ≤ 2 * entanglementA P_AB * uA := by
        calc
          |eA₂| ≤ 2 * tvDist P_A P_true_A * uA := heA₂base
          _ = 2 * tvDist P_true_A P_A * uA := by rw [tvDist_comm]
          _ ≤ 2 * entanglementA P_AB * uA := by gcongr
      have heB₁ : |eB₁| ≤ 2 * entanglementB P_AB * uB := by
        dsimp [eB₁, uB]
        simpa [hP_B_opt] using agentB_action_bound P_AB P_B Q_true_B p
      have heB₂base : |eB₂| ≤ 2 * tvDist P_B P_true_B * uB := by
        dsimp [eB₂, uB]
        exact tv_action_bound P_B P_true_B Q_true_B p.2
      have heB₂ : |eB₂| ≤ 2 * entanglementB P_AB * uB := by
        calc
          |eB₂| ≤ 2 * tvDist P_B P_true_B * uB := heB₂base
          _ = 2 * tvDist P_true_B P_B * uB := by rw [tvDist_comm]
          _ ≤ 2 * entanglementB P_AB * uB := by gcongr
      rw [hDeq, abs_mul, abs_of_nonneg hγ0]
      calc
        γ * |sD + eA₁ + eA₂ + eB₁ + eB₂| ≤
            γ * (|sD| + |eA₁| + |eA₂| + |eB₁| + |eB₂|) := by
          gcongr
          calc
            |sD + eA₁ + eA₂ + eB₁ + eB₂| ≤
                |sD + eA₁ + eA₂ + eB₁| + |eB₂| := abs_add_le _ _
            _ ≤ (|sD + eA₁ + eA₂| + |eB₁|) + |eB₂| := by
              gcongr
              exact abs_add_le _ _
            _ ≤ ((|sD + eA₁| + |eA₂|) + |eB₁|) + |eB₂| := by
              gcongr
              exact abs_add_le _ _
            _ ≤ (((|sD| + |eA₁|) + |eA₂|) + |eB₁|) + |eB₂| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ γ *
            (u + (2 * entanglementA P_AB * uA) + (2 * entanglementA P_AB * uA) +
              (2 * entanglementB P_AB * uB) + (2 * entanglementB P_AB * uB)) := by
          gcongr
        _ = γ * u +
            4 * γ * (entanglementA P_AB * uA + entanglementB P_AB * uB) := by ring
    have hu : u ≤ γ * u +
        4 * γ * (entanglementA P_AB * uA + entanglementB P_AB * uB) :=
      ciSup_le hpoint
    have hden : 0 < 1 - γ := sub_pos.mpr hγ1
    have hu' : u ≤
        (4 * γ * (entanglementA P_AB * uA + entanglementB P_AB * uB)) / (1 - γ) := by
      apply (le_div_iff₀ hden).2
      nlinarith
    dsimp [D, u] at hu' ⊢
    calc
      (⨆ p : SA × SB, |Q_AB p - (Q_true_A p.1 + Q_true_B p.2)|) ≤
          (4 * γ * (entanglementA P_AB * uA + entanglementB P_AB * uB)) / (1 - γ) := hu'
      _ ≤ (4 * γ *
          (entanglementA P_AB * (rAmax / (1 - γ)) +
            entanglementB P_AB * (rBmax / (1 - γ)))) / (1 - γ) := by
        gcongr
      _ = 4 * γ * (entanglementA P_AB * rAmax + entanglementB P_AB * rBmax) /
          (1 - γ) ^ 2 := by
        field_simp
        <;> ring
  · haveI : IsEmpty (SA × SB) := not_nonempty_iff.mp hp
    simp [entanglementA, entanglementB, agentTVDistA, agentTVDistB]
