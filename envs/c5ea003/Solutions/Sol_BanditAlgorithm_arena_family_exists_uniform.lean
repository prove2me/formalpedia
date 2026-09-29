-- Prove2me | solution 1 for BanditAlgorithm.arena_family_exists_uniform
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T07:49:31.08107+00:00
-- url     : https://prove2.me/submissions/d33fcf8f-08b3-411c-b8d7-df58c0c8f298

-- Ported from ryanshin accepted submission 74c6a5c9-12c7-4f1b-ab83-527b8e2644fa.
import Definitions.Def_LayeredArena
import Theorems.Thm_BanditAlgorithm_mdp_travel_time_le_of_lyapunov_drift

open MeasureTheory ProbabilityTheory
open scoped NNReal
open BanditAlgorithm BanditAlgorithm.LayeredArena



/-- `T A j = 1 + A + ... + A^(j-1)`: the index of the first node at heap level `j`. -/
def ArenaFam.T (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => A * T A j + 1

open ArenaFam

/-- Heap level of node `i`: `lvlH 0 = 0`, `lvlH i = lvlH ((i-1)/A) + 1`. -/
def ArenaFam.lvlH (A : ℕ) (i : ℕ) : ℕ :=
  if h : i = 0 then 0 else
    have : (i - 1) / A < i := by
      rcases Nat.eq_zero_or_pos A with hA | hA
      · subst hA; simp; omega
      · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    lvlH A ((i - 1) / A) + 1
decreasing_by exact this

theorem ArenaFam.lvlH_zero (A : ℕ) : lvlH A 0 = 0 := by rw [lvlH]; simp

theorem ArenaFam.lvlH_succ (A : ℕ) (i : ℕ) (hi : i ≠ 0) : lvlH A i = lvlH A ((i - 1) / A) + 1 := by
  rw [lvlH]; simp [hi]

theorem ArenaFam.lvlH_child (A : ℕ) (hA : 0 < A) (i a : ℕ) (ha : a < A) :
    lvlH A (A * i + 1 + a) = lvlH A i + 1 := by
  rw [lvlH_succ A _ (by omega)]
  congr 2
  have : A * i + 1 + a - 1 = a + A * i := by omega
  rw [this, Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt ha, zero_add]

theorem ArenaFam.lvlH_mono (A : ℕ) : Monotone (lvlH A) := by
  intro i j hij
  induction j using Nat.strong_induction_on generalizing i with
  | _ j ih =>
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; rw [lvlH_zero]; exact Nat.zero_le _
    · have hj : j ≠ 0 := by omega
      rw [lvlH_succ A i (by omega), lvlH_succ A j hj]
      have h1 : (i - 1) / A ≤ (j - 1) / A := Nat.div_le_div_right (by omega)
      have h2 : (j - 1) / A < j := by
        rcases Nat.eq_zero_or_pos A with hA | hA
        · subst hA; simp; omega
        · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      exact Nat.succ_le_succ (ih _ h2 h1)

theorem ArenaFam.T_succ (A j : ℕ) : T A (j + 1) = A * T A j + 1 := rfl

theorem ArenaFam.T_strictMono (A : ℕ) (hA : 0 < A) : StrictMono (T A) := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [T_succ]
  nlinarith [Nat.zero_le (T A j)]

theorem ArenaFam.T_mono (A : ℕ) (hA : 0 < A) : Monotone (T A) := (T_strictMono A hA).monotone

/-- `T (lvlH i) ≤ i < T (lvlH i + 1)`. -/
theorem ArenaFam.T_lvlH (A : ℕ) (hA : 0 < A) (i : ℕ) :
    T A (lvlH A i) ≤ i ∧ i < T A (lvlH A i + 1) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi; rw [lvlH_zero]; simp [T]
    · have hp : (i - 1) / A < i := lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
      obtain ⟨h1, h2⟩ := ih _ hp
      rw [lvlH_succ A i (by omega), T_succ, T_succ]
      have h3 : A * ((i - 1) / A) ≤ i - 1 := Nat.mul_div_le _ _
      have h4 : i - 1 < A * ((i - 1) / A) + A := by
        have := Nat.lt_mul_div_succ (i - 1) hA
        rw [Nat.mul_add, Nat.mul_one] at this
        exact this
      have h5 := Nat.mul_le_mul_left A h1
      have h6 := Nat.mul_le_mul_left A (Nat.succ_le_of_lt h2)
      rw [Nat.mul_succ] at h6
      constructor
      · omega
      · omega

theorem ArenaFam.lvlH_eq_of_T (A : ℕ) (hA : 0 < A) (i j : ℕ) (h1 : T A j ≤ i) (h2 : i < T A (j + 1)) :
    lvlH A i = j := by
  obtain ⟨h3, h4⟩ := T_lvlH A hA i
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := T_mono A hA (show lvlH A i + 1 ≤ j from h); omega
  · have := T_mono A hA (show j + 1 ≤ lvlH A i from h); omega

theorem ArenaFam.T_ge_pow (A : ℕ) (hA : 0 < A) (j : ℕ) : A ^ j ≤ T A (j + 1) := by
  induction j with
  | zero => simp [T]
  | succ j ih => rw [T_succ, pow_succ]; nlinarith

theorem ArenaFam.lvlH_ge_iff (A : ℕ) (hA : 0 < A) (i j : ℕ) : j ≤ lvlH A i ↔ T A j ≤ i := by
  obtain ⟨h3, h4⟩ := T_lvlH A hA i
  constructor
  · intro h; exact le_trans (T_mono A hA h) h3
  · intro h; by_contra hlt; push_neg at hlt
    have := T_mono A hA (show lvlH A i + 1 ≤ j from hlt); omega



theorem ArenaFam.T_succ_eq (A j : ℕ) : T A (j + 1) = T A j + A ^ j := by
  induction j with
  | zero => simp [T]
  | succ j ih =>
    have h := ih
    rw [T_succ] at h
    rw [T_succ A (j + 1), ih, pow_succ, Nat.mul_add, ← h]
    ring

/-! ## Parameters of the skeleton -/

/-- depth -/
def ArenaFam.dOf (A n : ℕ) : ℕ := lvlH A (n - 1)
/-- first index of level `d - 1` -/
def ArenaFam.TprevOf (A n : ℕ) : ℕ := T A (dOf A n - 1)
/-- nodes on the two last levels -/
def ArenaFam.ROf (A n : ℕ) : ℕ := n - TprevOf A n
/-- internal nodes on level `d - 1` -/
def ArenaFam.IOf (A n : ℕ) : ℕ := (ROf A n + A) / (A + 1)
/-- number of internal nodes -/
def ArenaFam.KOf (A n : ℕ) : ℕ := if n = 1 then 0 else TprevOf A n + IOf A n

section facts
variable {A n : ℕ} (hA : 2 ≤ A) (hn : 2 ≤ n)
include hA hn

theorem ArenaFam.d_pos : 1 ≤ dOf A n := by
  unfold dOf
  rw [lvlH_succ A (n - 1) (by omega)]
  omega

theorem ArenaFam.Td_le : T A (dOf A n) ≤ n - 1 := (T_lvlH A (by omega) (n - 1)).1
theorem ArenaFam.lt_Td_succ : n - 1 < T A (dOf A n + 1) := (T_lvlH A (by omega) (n - 1)).2

theorem ArenaFam.Td_eq : T A (dOf A n) = A * TprevOf A n + 1 := by
  unfold TprevOf
  have := d_pos hA hn
  conv_lhs => rw [show dOf A n = (dOf A n - 1) + 1 by omega]
  rfl

theorem ArenaFam.Td_eq' : T A (dOf A n) = TprevOf A n + A ^ (dOf A n - 1) := by
  unfold TprevOf
  have := d_pos hA hn
  conv_lhs => rw [show dOf A n = (dOf A n - 1) + 1 by omega]
  exact T_succ_eq A _

theorem ArenaFam.R_ge : 2 ≤ ROf A n := by
  unfold ROf
  have h1 := Td_le hA hn
  have h2 := Td_eq hA hn
  have : TprevOf A n ≤ A * TprevOf A n := Nat.le_mul_of_pos_left _ (by omega)
  omega

theorem ArenaFam.I_pos : 1 ≤ IOf A n := by
  unfold IOf
  have := R_ge hA hn
  rw [Nat.le_div_iff_mul_le (by omega)]
  omega

theorem ArenaFam.I_lt_R : IOf A n < ROf A n := by
  unfold IOf
  have := R_ge hA hn
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  nlinarith

theorem ArenaFam.R_le_I : ROf A n ≤ (A + 1) * IOf A n := by
  unfold IOf
  have h := Nat.div_add_mod (ROf A n + A) (A + 1)
  have h2 := Nat.mod_lt (ROf A n + A) (show 0 < A + 1 by omega)
  omega

theorem ArenaFam.R_le_pow : ROf A n ≤ A ^ (dOf A n - 1) + A ^ (dOf A n) := by
  unfold ROf
  have h1 := lt_Td_succ hA hn
  have h2 := T_succ_eq A (dOf A n)
  have h3 := Td_eq' hA hn
  omega

theorem ArenaFam.I_le_pow : IOf A n ≤ A ^ (dOf A n - 1) := by
  unfold IOf
  have h1 := R_le_pow hA hn
  have hd := d_pos hA hn
  have h2 : A ^ (dOf A n) = A * A ^ (dOf A n - 1) := by
    conv_lhs => rw [show dOf A n = (dOf A n - 1) + 1 by omega]
    rw [pow_succ]; ring
  have : ROf A n + A < (A ^ (dOf A n - 1) + 1) * (A + 1) := by nlinarith
  exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).2 this)

theorem ArenaFam.K_eq : KOf A n = TprevOf A n + IOf A n := by
  unfold KOf; rw [if_neg (by omega)]

theorem ArenaFam.K_le_Td : KOf A n ≤ T A (dOf A n) := by
  rw [K_eq hA hn, Td_eq' hA hn]
  have := I_le_pow hA hn
  omega

theorem ArenaFam.K_lt_n : KOf A n < n := by
  have := K_le_Td hA hn
  have := Td_le hA hn
  omega

theorem ArenaFam.Tprev_lt_K : TprevOf A n < KOf A n := by
  rw [K_eq hA hn]; have := I_pos hA hn; omega

theorem ArenaFam.lvlH_K_pred : lvlH A (KOf A n - 1) = dOf A n - 1 := by
  have hd := d_pos hA hn
  apply lvlH_eq_of_T A (by omega)
  · have := Tprev_lt_K hA hn; unfold TprevOf at this; omega
  · rw [show dOf A n - 1 + 1 = dOf A n by omega]
    have := K_le_Td hA hn
    have := Tprev_lt_K hA hn
    omega

theorem ArenaFam.L_le : n - KOf A n ≤ A * IOf A n := by
  rw [K_eq hA hn]
  have h1 := R_le_I hA hn
  unfold ROf at h1
  have h2 := Tprev_lt_K hA hn
  rw [K_eq hA hn] at h2
  have : (A + 1) * IOf A n = A * IOf A n + IOf A n := by ring
  omega

theorem ArenaFam.three_I_le : 3 * IOf A n ≤ ROf A n + 2 := by
  unfold IOf
  set R := ROf A n
  have hq := Nat.div_add_mod (R + 2) 3
  have hq2 := Nat.mod_lt (R + 2) (show 0 < 3 by omega)
  set q := (R + 2) / 3
  have h3q : R ≤ 3 * q := by omega
  have hAq : 3 * q ≤ (A + 1) * q := Nat.mul_le_mul_right _ (by omega)
  have : (R + A) / (A + 1) ≤ q := by
    apply Nat.lt_succ_iff.mp
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    nlinarith
  omega

theorem ArenaFam.n_le_three_L : n ≤ 3 * (n - KOf A n) + 1 := by
  rw [K_eq hA hn]
  have h1 := three_I_le hA hn
  have h2 := Td_le hA hn
  have h3 := Td_eq hA hn
  have h4 := I_lt_R hA hn
  unfold ROf at h1 h4
  have : TprevOf A n ≤ A * TprevOf A n := Nat.le_mul_of_pos_left _ (by omega)
  have : 2 * TprevOf A n ≤ A * TprevOf A n := Nat.mul_le_mul_right _ hA
  omega

theorem ArenaFam.pow_d_lt : A ^ (dOf A n) < A * n := by
  have hd := d_pos hA hn
  have h1 := T_ge_pow A (by omega) (dOf A n - 1)
  rw [show dOf A n - 1 + 1 = dOf A n by omega] at h1
  have h2 := Td_le hA hn
  have h3 : A ^ (dOf A n) = A * A ^ (dOf A n - 1) := by
    conv_lhs => rw [show dOf A n = (dOf A n - 1) + 1 by omega]
    rw [pow_succ]; ring
  rw [h3]
  exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)

end facts

theorem ArenaFam.d_one (A : ℕ) : dOf A 1 = 0 := by unfold dOf; simp [lvlH_zero]
theorem ArenaFam.K_one (A : ℕ) : KOf A 1 = 0 := by unfold KOf; simp

/-! ## The tree on `ℕ` indices -/

/-- level of node `i` -/
def ArenaFam.lvlN (A n : ℕ) (i : ℕ) : ℕ := if i < KOf A n then lvlH A i else dOf A n

/-- child of node `i` by action `a` -/
def ArenaFam.childN (A n : ℕ) (i a : ℕ) : ℕ :=
  if i < TprevOf A n then (if A * i + 1 + a < KOf A n then A * i + 1 + a else KOf A n - 1)
  else if i < KOf A n then
    (if KOf A n + (i - TprevOf A n) * A + a < n then KOf A n + (i - TprevOf A n) * A + a
      else n - 1)
  else i

/-- parent of node `t ≥ 1` -/
def ArenaFam.parN (A n : ℕ) (t : ℕ) : ℕ :=
  if t < KOf A n then (t - 1) / A else TprevOf A n + (t - KOf A n) / A

/-- action from the parent of `t` leading to `t` -/
def ArenaFam.actN (A n : ℕ) (t : ℕ) : ℕ :=
  if t < KOf A n then (t - 1) % A else (t - KOf A n) % A

theorem ArenaFam.actN_lt (A n : ℕ) (hA : 0 < A) (t : ℕ) : actN A n t < A := by
  unfold actN; split_ifs <;> exact Nat.mod_lt _ hA

theorem ArenaFam.lvlN_of_lt {A n i : ℕ} (h : i < KOf A n) : lvlN A n i = lvlH A i := if_pos h
theorem ArenaFam.lvlN_of_ge {A n i : ℕ} (h : KOf A n ≤ i) : lvlN A n i = dOf A n := if_neg (not_lt.2 h)

theorem ArenaFam.parN_of_lt {A n t : ℕ} (h : t < KOf A n) : parN A n t = (t - 1) / A := if_pos h
theorem ArenaFam.parN_of_ge {A n t : ℕ} (h : KOf A n ≤ t) :
    parN A n t = TprevOf A n + (t - KOf A n) / A := if_neg (not_lt.2 h)
theorem ArenaFam.actN_of_lt {A n t : ℕ} (h : t < KOf A n) : actN A n t = (t - 1) % A := if_pos h
theorem ArenaFam.actN_of_ge {A n t : ℕ} (h : KOf A n ≤ t) : actN A n t = (t - KOf A n) % A :=
  if_neg (not_lt.2 h)

section tree
variable {A n : ℕ} (hA : 2 ≤ A) (hn : 2 ≤ n)
include hA hn

theorem ArenaFam.lvlN_lt_of_lt {i : ℕ} (h : i < KOf A n) : lvlN A n i < dOf A n := by
  rw [lvlN_of_lt h]
  have := lvlH_mono A (show i ≤ KOf A n - 1 by omega)
  rw [lvlH_K_pred hA hn] at this
  have := d_pos hA hn
  omega

theorem ArenaFam.lt_K_of_lvlN_lt {i : ℕ} (h : lvlN A n i < dOf A n) : i < KOf A n := by
  by_contra h'; rw [lvlN_of_ge (not_lt.1 h')] at h; exact lt_irrefl _ h

theorem ArenaFam.lvlH_lt_of_lt_Tprev {i : ℕ} (h : i < TprevOf A n) : lvlH A i < dOf A n - 1 := by
  by_contra h'
  push_neg at h'
  have := (lvlH_ge_iff A (by omega) i (dOf A n - 1)).1 h'
  unfold TprevOf at h; omega

theorem ArenaFam.lvlH_eq_of_Tprev_le {i : ℕ} (h1 : TprevOf A n ≤ i) (h2 : i < KOf A n) :
    lvlH A i = dOf A n - 1 := by
  have h3 := (lvlH_ge_iff A (by omega) i (dOf A n - 1)).2 h1
  have h4 := lvlH_mono A (show i ≤ KOf A n - 1 by omega)
  rw [lvlH_K_pred hA hn] at h4
  omega

theorem ArenaFam.childN_lt {i a : ℕ} (hi : i < n) : childN A n i a < n := by
  have hK := K_lt_n hA hn
  unfold childN
  split_ifs <;> omega

theorem ArenaFam.lvlN_childN {i a : ℕ} (ha : a < A) (hl : lvlN A n i < dOf A n) :
    lvlN A n (childN A n i a) = lvlN A n i + 1 := by
  have hK := K_lt_n hA hn
  have hiK := lt_K_of_lvlN_lt hA hn hl
  have hd := d_pos hA hn
  rw [lvlN_of_lt hiK]
  unfold childN
  by_cases h1 : i < TprevOf A n
  · rw [if_pos h1]
    have hlt := lvlH_lt_of_lt_Tprev hA hn h1
    have hch := lvlH_child A (by omega) i a ha
    by_cases h2 : A * i + 1 + a < KOf A n
    · rw [if_pos h2, lvlN_of_lt h2, hch]
    · rw [if_neg h2, lvlN_of_lt (show KOf A n - 1 < KOf A n by omega), lvlH_K_pred hA hn]
      have := lvlH_mono A (show KOf A n - 1 ≤ A * i + 1 + a by omega)
      rw [lvlH_K_pred hA hn, hch] at this
      omega
  · rw [if_neg h1, if_pos hiK]
    have := lvlH_eq_of_Tprev_le hA hn (not_lt.1 h1) hiK
    rw [this]
    split_ifs with h3
    · rw [lvlN_of_ge (by omega)]; omega
    · rw [lvlN_of_ge (by omega)]; omega

theorem ArenaFam.parN_lt {t : ℕ} (ht : 1 ≤ t) (htn : t < n) : parN A n t < t := by
  unfold parN
  have hTK := Tprev_lt_K hA hn
  split_ifs with h
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  · have := Nat.div_le_self (t - KOf A n) A; omega

theorem ArenaFam.parN_lt_K {t : ℕ} (ht : 1 ≤ t) (htn : t < n) : parN A n t < KOf A n := by
  unfold parN
  have hTK := Tprev_lt_K hA hn
  have hK := K_eq hA hn
  split_ifs with h
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  · have hL := L_le hA hn
    have : (t - KOf A n) / A < IOf A n := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have : t - KOf A n < n - KOf A n := by omega
      nlinarith
    omega

theorem ArenaFam.childN_parN {t : ℕ} (ht : 1 ≤ t) (htn : t < n) :
    childN A n (parN A n t) (actN A n t) = t := by
  have hTK := Tprev_lt_K hA hn
  have hKT := K_le_Td hA hn
  have hTd := Td_eq hA hn
  have hpK := parN_lt_K hA hn ht htn
  by_cases h : t < KOf A n
  · rw [parN_of_lt h, actN_of_lt h]
    unfold childN
    have hp : (t - 1) / A < TprevOf A n := by
      rw [Nat.div_lt_iff_lt_mul (by omega), Nat.mul_comm]
      omega
    rw [if_pos hp]
    have := Nat.div_add_mod (t - 1) A
    rw [if_pos (by omega)]
    omega
  · have h' := not_lt.1 h
    rw [parN_of_ge h', actN_of_ge h']
    rw [parN_of_ge h'] at hpK
    unfold childN
    rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)), if_pos hpK]
    have hdm := Nat.div_add_mod' (t - KOf A n) A
    have e1 : TprevOf A n + (t - KOf A n) / A - TprevOf A n = (t - KOf A n) / A :=
      Nat.add_sub_cancel_left _ _
    have e2 : KOf A n + (t - KOf A n) / A * A + (t - KOf A n) % A = t := by
      generalize (t - KOf A n) / A * A = q at hdm ⊢
      generalize (t - KOf A n) % A = r at hdm ⊢
      omega
    rw [e1, e2, if_pos htn]

end tree

/-! ## Versions valid for all `n ≥ 1` -/

theorem ArenaFam.childN_lt' {A n : ℕ} (hA : 2 ≤ A) (hn : 1 ≤ n) {i a : ℕ} (hi : i < n) :
    childN A n i a < n := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    unfold childN
    have hT : TprevOf A 1 = 0 := by unfold TprevOf; rw [d_one]; rfl
    rw [hT, K_one]; simp; omega
  · exact childN_lt hA h2 hi

theorem ArenaFam.lvlN_zero' {A n : ℕ} (hA : 2 ≤ A) (hn : 1 ≤ n) : lvlN A n 0 = 0 := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    unfold lvlN; rw [K_one, d_one]; simp
  · rw [lvlN_of_lt (by have := Tprev_lt_K hA h2; omega)]; exact lvlH_zero A

theorem ArenaFam.lvlN_le' {A n : ℕ} (hA : 2 ≤ A) (hn : 1 ≤ n) (i : ℕ) : lvlN A n i ≤ dOf A n := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    unfold lvlN; rw [K_one]; simp
  · by_cases h : i < KOf A n
    · exact le_of_lt (lvlN_lt_of_lt hA h2 h)
    · rw [lvlN_of_ge (not_lt.1 h)]

theorem ArenaFam.lvlN_childN' {A n : ℕ} (hA : 2 ≤ A) (hn : 1 ≤ n) {i a : ℕ} (ha : a < A)
    (hl : lvlN A n i < dOf A n) : lvlN A n (childN A n i a) = lvlN A n i + 1 := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    exfalso; rw [d_one] at hl; exact Nat.not_lt_zero _ hl
  · exact lvlN_childN hA h2 ha hl

theorem ArenaFam.lvlN_eq_d_iff' {A n : ℕ} (hA : 2 ≤ A) (hn : 1 ≤ n) {i : ℕ} :
    lvlN A n i = dOf A n ↔ KOf A n ≤ i := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1
    unfold lvlN; rw [K_one]; simp
  · constructor
    · intro h
      by_contra h'
      have := lvlN_lt_of_lt hA h2 (not_le.1 h')
      omega
    · intro h; exact lvlN_of_ge h

theorem ArenaFam.K_lt_n' {A n : ℕ} (hA : 2 ≤ A) (hn : 1 ≤ n) : KOf A n < n := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1; rw [K_one]; omega
  · exact K_lt_n hA h2

theorem ArenaFam.pow_d_lt' {A n : ℕ} (hA : 2 ≤ A) (hn : 1 ≤ n) : A ^ (dOf A n) < A * n := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1; rw [d_one]; simp; omega
  · exact pow_d_lt hA h2

theorem ArenaFam.n_le_three_L' {A n : ℕ} (hA : 2 ≤ A) (hn : 1 ≤ n) : n ≤ 3 * (n - KOf A n) + 1 := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · have hn1 : n = 1 := by omega
    subst hn1; rw [K_one]; norm_num
  · exact n_le_three_L hA h2


variable {S A : ℕ}


/-- The combinatorial skeleton shared by all members of the family. -/
structure ArenaFam.Skel (S A : ℕ) where
  depth : ℕ
  good : Fin S
  bad : Fin S
  root : Fin S
  lvl : Fin S → ℕ
  child : Fin S → Fin A → Fin S
  good_ne_bad : good ≠ bad
  root_ne_good : root ≠ good
  root_ne_bad : root ≠ bad
  lvl_root : lvl root = 0
  lvl_le : ∀ s, s ≠ good → s ≠ bad → lvl s ≤ depth
  lvl_child : ∀ s a, s ≠ good → s ≠ bad → lvl s < depth → lvl (child s a) = lvl s + 1
  child_ne_good : ∀ s a, s ≠ good → s ≠ bad → lvl s < depth → child s a ≠ good
  child_ne_bad : ∀ s a, s ≠ good → s ≠ bad → lvl s < depth → child s a ≠ bad

/-- `t` is reachable from `s` by at most `m` child steps through internal nodes. -/
def ArenaFam.reachB (K : Skel S A) : ℕ → Fin S → Fin S → Bool
  | 0, s, t => decide (s = t)
  | m + 1, s, t => decide (s = t) ||
      (decide (s ≠ K.good ∧ s ≠ K.bad ∧ K.lvl s < K.depth) &&
        decide (∃ a : Fin A, reachB K m (K.child s a) t = true))

theorem ArenaFam.reachB_zero (K : Skel S A) (s t : Fin S) : reachB K 0 s t = true ↔ s = t := by
  simp [reachB]

theorem ArenaFam.reachB_succ (K : Skel S A) (m : ℕ) (s t : Fin S) : reachB K (m + 1) s t = true ↔
    s = t ∨ ((s ≠ K.good ∧ s ≠ K.bad ∧ K.lvl s < K.depth) ∧
      ∃ a, reachB K m (K.child s a) t = true) := by
  simp only [reachB, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem ArenaFam.reachB_refl (K : Skel S A) (m : ℕ) (s : Fin S) : reachB K m s s = true := by
  cases m <;> simp [reachB]

theorem ArenaFam.reachB_mono (K : Skel S A) {m : ℕ} {s t : Fin S} (h : reachB K m s t = true) :
    reachB K (m + 1) s t = true := by
  induction m generalizing s with
  | zero => rw [reachB_zero] at h; subst h; exact reachB_refl _ _ _
  | succ m ih =>
    rw [reachB_succ] at h ⊢
    rcases h with h | ⟨hs, a, ha⟩
    · exact Or.inl h
    · exact Or.inr ⟨hs, a, ih ha⟩

theorem ArenaFam.reachB_le (K : Skel S A) {m m' : ℕ} {s t : Fin S} (hmm : m ≤ m')
    (h : reachB K m s t = true) : reachB K m' s t = true := by
  induction hmm with
  | refl => exact h
  | step _ ih => exact reachB_mono _ ih

theorem ArenaFam.reachB_of_not_internal (K : Skel S A) {m : ℕ} {s t : Fin S}
    (hs : ¬ (s ≠ K.good ∧ s ≠ K.bad ∧ K.lvl s < K.depth))
    (h : reachB K m s t = true) : s = t := by
  cases m with
  | zero => exact (reachB_zero _ _ _).1 h
  | succ m =>
    rcases (reachB_succ _ _ _ _).1 h with h | ⟨hs', _⟩
    · exact h
    · exact absurd hs' hs

theorem ArenaFam.reachB_lvl_le (K : Skel S A) {m : ℕ} {s t : Fin S} (h : reachB K m s t = true) :
    K.lvl s ≤ K.lvl t := by
  induction m generalizing s with
  | zero => rw [(reachB_zero _ _ _).1 h]
  | succ m ih =>
    rcases (reachB_succ _ _ _ _).1 h with h | ⟨⟨hg, hb, hl⟩, a, ha⟩
    · rw [h]
    · have := ih ha
      rw [K.lvl_child s a hg hb hl] at this
      omega

theorem ArenaFam.reachB_step (K : Skel S A) {m : ℕ} {s t : Fin S} (a : Fin A)
    (hs : s ≠ K.good ∧ s ≠ K.bad ∧ K.lvl s < K.depth)
    (h : reachB K m (K.child s a) t = true) : reachB K (m + 1) s t = true :=
  (reachB_succ _ _ _ _).2 (Or.inr ⟨hs, a, h⟩)

theorem ArenaFam.reachB_sat (K : Skel S A) {m : ℕ} {s t : Fin S} (h : reachB K m s t = true) :
    reachB K (K.depth - K.lvl s) s t = true := by
  induction m generalizing s with
  | zero => rw [(reachB_zero _ _ _).1 h]; exact reachB_refl _ _ _
  | succ m ih =>
    rcases (reachB_succ _ _ _ _).1 h with h | ⟨⟨hg, hb, hl⟩, a, ha⟩
    · rw [h]; exact reachB_refl _ _ _
    · have h1 := ih ha
      rw [K.lvl_child s a hg hb hl] at h1
      have : K.depth - K.lvl s = (K.depth - (K.lvl s + 1)) + 1 := by omega
      rw [this]
      exact reachB_step _ a ⟨hg, hb, hl⟩ h1

theorem ArenaFam.reachB_snoc (K : Skel S A) {m : ℕ} {s c : Fin S} (h : reachB K m s c = true)
    (hc : c ≠ K.good ∧ c ≠ K.bad ∧ K.lvl c < K.depth) (a : Fin A) :
    reachB K (m + 1) s (K.child c a) = true := by
  induction m generalizing s with
  | zero => rw [(reachB_zero _ _ _).1 h]; exact reachB_step _ a hc (reachB_refl _ _ _)
  | succ m ih =>
    rcases (reachB_succ _ _ _ _).1 h with h | ⟨hs, b, hb⟩
    · subst h; exact reachB_step _ a hc (reachB_refl _ _ _)
    · exact reachB_step _ b hs (ih hb)

/-- Reachability with the canonical fuel `depth`. -/
theorem ArenaFam.reachB_depth (K : Skel S A) {m : ℕ} {s t : Fin S} (h : reachB K m s t = true) :
    reachB K K.depth s t = true :=
  reachB_le _ (Nat.sub_le _ _) (reachB_sat _ h)

/-- Build a layered arena from a skeleton and a special leaf reachable from the root. -/
noncomputable def ArenaFam.mkArena (K : Skel S A) (spec : Fin S) (act dflt : Fin A)
    (hg : spec ≠ K.good) (hb : spec ≠ K.bad) (hlvl : K.lvl spec = K.depth)
    (hreach : reachB K K.depth K.root spec = true) : LayeredArena S A where
  depth := K.depth
  good := K.good
  bad := K.bad
  root := K.root
  specialLeaf := spec
  specialAction := act
  defaultAction := dflt
  lvl := K.lvl
  child := K.child
  onPath := fun s => reachB K K.depth s spec
  pathAction := fun s =>
    if h : ∃ a, reachB K K.depth (K.child s a) spec = true then h.choose else dflt
  good_ne_bad := K.good_ne_bad
  root_ne_good := K.root_ne_good
  root_ne_bad := K.root_ne_bad
  lvl_root := K.lvl_root
  lvl_le := K.lvl_le
  lvl_child := K.lvl_child
  child_ne_good := K.child_ne_good
  child_ne_bad := K.child_ne_bad
  onPath_root := hreach
  onPath_child_mp := by
    intro s a hg' hb' hl h
    have h1 := reachB_sat K h
    rw [K.lvl_child s a hg' hb' hl] at h1
    have : K.depth - K.lvl s = (K.depth - (K.lvl s + 1)) + 1 := by omega
    exact reachB_depth K (this ▸ reachB_step K a ⟨hg', hb', hl⟩ h1)
  onPath_child_mpr := by
    intro s hg' hb' hl h
    have hne : s ≠ spec := by
      intro hs; rw [hs, hlvl] at hl; exact lt_irrefl _ hl
    obtain ⟨m, hm⟩ : ∃ m, K.depth = m + 1 := ⟨K.depth - 1, by omega⟩
    rw [hm] at h
    rcases (reachB_succ _ _ _ _).1 h with h | ⟨_, a, ha⟩
    · exact absurd h hne
    · have hex : ∃ a, reachB K K.depth (K.child s a) spec = true :=
        ⟨a, hm ▸ reachB_mono K ha⟩
      rw [dif_pos hex]
      exact hex.choose_spec
  onPath_leaf := by
    intro s hg' hb' hl h
    exact reachB_of_not_internal K (fun h' => by omega) h
  specialLeaf_ne_good := hg
  specialLeaf_ne_bad := hb
  specialLeaf_lvl := hlvl
  onPath_specialLeaf := reachB_refl _ _ _

/-- The skeleton of a layered arena. -/
def ArenaFam.skelOf (E : LayeredArena S A) : Skel S A :=
  ⟨E.depth, E.good, E.bad, E.root, E.lvl, E.child, E.good_ne_bad, E.root_ne_good,
    E.root_ne_bad, E.lvl_root, E.lvl_le, E.lvl_child, E.child_ne_good, E.child_ne_bad⟩

theorem ArenaFam.skel_mkArena (K : Skel S A) (spec : Fin S) (act dflt : Fin A)
    (hg : spec ≠ K.good) (hb : spec ≠ K.bad) (hlvl : K.lvl spec = K.depth)
    (hreach : reachB K K.depth K.root spec = true) :
    skelOf (mkArena K spec act dflt hg hb hlvl hreach) = K := rfl

/-- The one-step drift sum of the arena MDP. -/
theorem ArenaFam.drift_sum [NeZero S] (E : LayeredArena S A) {δ Δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hΔ2 : Δ ≤ 1 / 2) (V : Fin S → ℝ) (s : Fin S) (a : Fin A) :
    ∑ s', ((E.toMDP hδ1 hΔ2).P s a s' : ℝ) * V s' =
      if s = E.good then (1 - (δ : ℝ)) * V E.good + (δ : ℝ) * V E.root
      else if s = E.bad then (1 - (δ : ℝ)) * V E.bad + (δ : ℝ) * V E.root
      else if E.lvl s < E.depth then V (E.child s a)
      else (E.goodProb Δ s a : ℝ) * V E.good + (1 - (E.goodProb Δ s a : ℝ)) * V E.bad := by
  change ∑ s', ((E.rows δ Δ s a s' : ℝ≥0) : ℝ) * V s' = _
  simp only [rows]
  split_ifs <;> rw [sum_twoPoint_mul]
  · rw [NNReal.coe_sub hδ1]; push_cast; ring
  · rw [NNReal.coe_sub hδ1]; push_cast; ring
  · push_cast; ring
  · rw [NNReal.coe_sub (E.goodProb_le_one hΔ2 s a)]; push_cast; ring

theorem ArenaFam.goodProb_coe_bounds (E : LayeredArena S A) {Δ : ℝ≥0} (hΔ4 : Δ ≤ 1 / 4) (s : Fin S)
    (a : Fin A) : (1 / 2 : ℝ) ≤ (E.goodProb Δ s a : ℝ) ∧ (E.goodProb Δ s a : ℝ) ≤ 3 / 4 := by
  have hΔ : (Δ : ℝ) ≤ 1 / 4 := by exact_mod_cast hΔ4
  unfold goodProb
  split_ifs <;> push_cast <;> constructor <;> linarith [Δ.coe_nonneg]


@[simp] theorem ArenaFam.skel_depth (E : LayeredArena S A) : (skelOf E).depth = E.depth := rfl
@[simp] theorem ArenaFam.skel_good (E : LayeredArena S A) : (skelOf E).good = E.good := rfl
@[simp] theorem ArenaFam.skel_bad (E : LayeredArena S A) : (skelOf E).bad = E.bad := rfl
@[simp] theorem ArenaFam.skel_root (E : LayeredArena S A) : (skelOf E).root = E.root := rfl
@[simp] theorem ArenaFam.skel_lvl (E : LayeredArena S A) : (skelOf E).lvl = E.lvl := rfl
@[simp] theorem ArenaFam.skel_child (E : LayeredArena S A) : (skelOf E).child = E.child := rfl

/-- The diameter bound: every tree node reachable from the root, `Δ ≤ 1/4`. -/
theorem ArenaFam.diameter_le [NeZero S] (E : LayeredArena S A) {δ Δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hΔ2 : Δ ≤ 1 / 2) (hδ0 : (0 : ℝ) < δ) (hΔ4 : Δ ≤ 1 / 4)
    (hreach : ∀ t, t ≠ E.good → t ≠ E.bad → reachB (skelOf E) E.depth E.root t = true) :
    mdpDiameterENN (E.toMDP hδ1 hΔ2) ≤ ENNReal.ofReal (4 * E.epiLen (δ : ℝ)) := by
  unfold mdpDiameterENN
  refine iSup_le fun src => iSup_le fun tgt => iSup_le fun hne => ?_
  set c : ℝ := 1 / (δ : ℝ) with hc
  have hδc : (δ : ℝ) * c = 1 := mul_one_div_cancel (ne_of_gt hδ0)
  have hc0 : 0 ≤ c := by positivity
  have hδ0' : (0 : ℝ) ≤ δ := le_of_lt hδ0
  have hepi : E.epiLen (δ : ℝ) = c + E.depth + 1 := rfl
  have hp := fun s a => goodProb_coe_bounds E hΔ4 s a
  have hd0 : (0 : ℝ) ≤ E.depth := Nat.cast_nonneg _
  have hlvl_le : ∀ s, s ≠ E.good → s ≠ E.bad → (E.lvl s : ℝ) ≤ E.depth := fun s h1 h2 => by
    exact_mod_cast E.lvl_le s h1 h2
  rw [hepi]
  by_cases htg : tgt = E.good
  · subst htg
    let V : Fin S → ℝ := fun s => if s = E.good then 0 else if s = E.bad
      then 2 * c + 2 * E.depth + 2 else c + 2 * E.depth + 2 - E.lvl s
    have hVg : V E.good = 0 := by simp [V]
    have hVb : V E.bad = 2 * c + 2 * E.depth + 2 := by simp [V, E.good_ne_bad.symm]
    have hVr : V E.root = c + 2 * E.depth + 2 := by
      simp [V, E.root_ne_good, E.root_ne_bad, E.lvl_root]
    have hVn : ∀ s, s ≠ E.good → s ≠ E.bad → V s = c + 2 * E.depth + 2 - E.lvl s := by
      intro s h1 h2; simp [V, h1, h2]
    refine (iInf_le (fun f => mdpTravelTime (E.toMDP hδ1 hΔ2) f src E.good)
      (fun _ => E.defaultAction)).trans ?_
    refine (mdp_travel_time_le_of_lyapunov_drift _ _ _ _ V ?_ ?_).trans
      (ENNReal.ofReal_le_ofReal ?_)
    · intro s
      by_cases h1 : s = E.good
      · rw [h1, hVg]
      by_cases h2 : s = E.bad
      · rw [h2, hVb]; linarith
      rw [hVn s h1 h2]; linarith [hlvl_le s h1 h2]
    · intro s hs
      rw [drift_sum, if_neg hs]
      by_cases hb : s = E.bad
      · rw [if_pos hb, hb, hVb, hVr]; nlinarith [hδc]
      · rw [if_neg hb]
        by_cases hl : E.lvl s < E.depth
        · rw [if_pos hl, hVn s hs hb,
            hVn _ (E.child_ne_good s _ hs hb hl) (E.child_ne_bad s _ hs hb hl),
            E.lvl_child s _ hs hb hl]
          push_cast; linarith
        · rw [if_neg hl, hVg, hVb, hVn s hs hb]
          have hle := E.lvl_le s hs hb
          have hlv : E.lvl s = E.depth := by omega
          rw [hlv]
          obtain ⟨hp1, hp2⟩ := hp s (E.defaultAction)
          nlinarith [mul_nonneg (sub_nonneg.2 hp1) (by positivity : (0:ℝ) ≤ 2 * c + 2 * E.depth + 2)]
    · by_cases h1 : src = E.good
      · rw [h1, hVg]; positivity
      by_cases h2 : src = E.bad
      · rw [h2, hVb]; linarith
      rw [hVn src h1 h2]; linarith [(Nat.cast_nonneg (E.lvl src) : (0:ℝ) ≤ E.lvl src)]
  by_cases htb : tgt = E.bad
  · subst htb
    let V : Fin S → ℝ := fun s => if s = E.bad then 0 else if s = E.good
      then 4 * c + 4 * E.depth + 4 else 3 * c + 4 * E.depth + 4 - E.lvl s
    have hVb : V E.bad = 0 := by simp [V]
    have hVg : V E.good = 4 * c + 4 * E.depth + 4 := by simp [V, E.good_ne_bad]
    have hVr : V E.root = 3 * c + 4 * E.depth + 4 := by
      simp [V, E.root_ne_good, E.root_ne_bad, E.lvl_root]
    have hVn : ∀ s, s ≠ E.good → s ≠ E.bad → V s = 3 * c + 4 * E.depth + 4 - E.lvl s := by
      intro s h1 h2; simp [V, h1, h2]
    refine (iInf_le (fun f => mdpTravelTime (E.toMDP hδ1 hΔ2) f src E.bad)
      (fun _ => E.defaultAction)).trans ?_
    refine (mdp_travel_time_le_of_lyapunov_drift _ _ _ _ V ?_ ?_).trans
      (ENNReal.ofReal_le_ofReal ?_)
    · intro s
      by_cases h2 : s = E.bad
      · rw [h2, hVb]
      by_cases h1 : s = E.good
      · rw [h1, hVg]; linarith
      rw [hVn s h1 h2]; linarith [hlvl_le s h1 h2]
    · intro s hs
      rw [drift_sum]
      by_cases hg : s = E.good
      · rw [if_pos hg, hg, hVg, hVr]; nlinarith [hδc]
      · rw [if_neg hg, if_neg hs]
        by_cases hl : E.lvl s < E.depth
        · rw [if_pos hl, hVn s hg hs,
            hVn _ (E.child_ne_good s _ hg hs hl) (E.child_ne_bad s _ hg hs hl),
            E.lvl_child s _ hg hs hl]
          push_cast; linarith
        · rw [if_neg hl, hVg, hVb, hVn s hg hs]
          have hle := E.lvl_le s hg hs
          have hlv : E.lvl s = E.depth := by omega
          rw [hlv]
          obtain ⟨hp1, hp2⟩ := hp s (E.defaultAction)
          nlinarith [mul_nonneg (sub_nonneg.2 hp2) (by positivity : (0:ℝ) ≤ 4 * c + 4 * E.depth + 4)]
    · by_cases h2 : src = E.bad
      · rw [h2, hVb]; positivity
      by_cases h1 : src = E.good
      · rw [h1, hVg]; linarith
      rw [hVn src h1 h2]; linarith [(Nat.cast_nonneg (E.lvl src) : (0:ℝ) ≤ E.lvl src)]
  -- tgt is a tree node
  set K := skelOf E with hK
  have hℓd : (E.lvl tgt : ℝ) ≤ E.depth := hlvl_le tgt htg htb
  have hℓ0 : (0 : ℝ) ≤ E.lvl tgt := Nat.cast_nonneg _
  let R : Fin S → Prop := fun s => reachB K E.depth s tgt = true
  let f : Fin S → Fin A := fun s =>
    if h : ∃ a, reachB K E.depth (E.child s a) tgt = true then h.choose else E.defaultAction
  let V : Fin S → ℝ := fun s => if s = tgt then 0 else if s = E.good ∨ s = E.bad
    then c + E.lvl tgt else if reachB K E.depth s tgt = true then (E.lvl tgt : ℝ) - E.lvl s
    else c + E.lvl tgt + 1 + E.depth - E.lvl s
  have hVt : V tgt = 0 := by simp [V]
  have hVg : V E.good = c + E.lvl tgt := by simp [V, Ne.symm htg]
  have hVb : V E.bad = c + E.lvl tgt := by simp [V, Ne.symm htb]
  have hVon : ∀ s, s ≠ tgt → s ≠ E.good → s ≠ E.bad → reachB K E.depth s tgt = true →
      V s = (E.lvl tgt : ℝ) - E.lvl s := by
    intro s h0 h1 h2 h3; simp [V, h0, h1, h2, h3]
  have hVoff : ∀ s, s ≠ tgt → s ≠ E.good → s ≠ E.bad → ¬ reachB K E.depth s tgt = true →
      V s = c + E.lvl tgt + 1 + E.depth - E.lvl s := by
    intro s h0 h1 h2 h3; simp [V, h0, h1, h2, h3]
  have hlvlR : ∀ s, reachB K E.depth s tgt = true → (E.lvl s : ℝ) ≤ E.lvl tgt := by
    intro s h; exact_mod_cast (reachB_lvl_le K h)
  have hVle : ∀ s, s ≠ E.good → s ≠ E.bad →
      V s ≤ c + E.lvl tgt + 1 + E.depth - E.lvl s := by
    intro s h1 h2
    by_cases h0 : s = tgt
    · rw [h0, hVt]; linarith
    by_cases h3 : reachB K E.depth s tgt = true
    · rw [hVon s h0 h1 h2 h3]; linarith
    · rw [hVoff s h0 h1 h2 h3]
  have hVr : V E.root ≤ E.lvl tgt := by
    by_cases h0 : E.root = tgt
    · rw [h0, hVt]; exact hℓ0
    · rw [hVon _ h0 E.root_ne_good E.root_ne_bad (hreach tgt htg htb), E.lvl_root]; simp
  have hVup : ∀ s, s ≠ tgt → s ≠ E.good → s ≠ E.bad → reachB K E.depth s tgt = true →
      V s ≤ (E.lvl tgt : ℝ) - E.lvl s := by
    intro s h0 h1 h2 h3; rw [hVon s h0 h1 h2 h3]
  have hVup' : ∀ s, s ≠ E.good → s ≠ E.bad → reachB K E.depth s tgt = true →
      V s ≤ (E.lvl tgt : ℝ) - E.lvl s := by
    intro s h1 h2 h3
    by_cases h0 : s = tgt
    · rw [h0, hVt]; simp
    · exact hVup s h0 h1 h2 h3
  refine (iInf_le (fun f => mdpTravelTime (E.toMDP hδ1 hΔ2) f src tgt) f).trans ?_
  refine (mdp_travel_time_le_of_lyapunov_drift _ _ _ _ V ?_ ?_).trans
    (ENNReal.ofReal_le_ofReal ?_)
  · intro s
    by_cases h0 : s = tgt
    · rw [h0, hVt]
    by_cases h1 : s = E.good
    · rw [h1, hVg]; linarith
    by_cases h2 : s = E.bad
    · rw [h2, hVb]; linarith
    by_cases h3 : reachB K E.depth s tgt = true
    · rw [hVon s h0 h1 h2 h3]; linarith [hlvlR s h3]
    · rw [hVoff s h0 h1 h2 h3]; linarith [hlvl_le s h1 h2]
  · intro s hs
    rw [drift_sum]
    by_cases hg : s = E.good
    · rw [if_pos hg, hg, hVg]
      nlinarith [hδc, mul_le_mul_of_nonneg_left hVr hδ0']
    rw [if_neg hg]
    by_cases hb : s = E.bad
    · rw [if_pos hb, hb, hVb]
      nlinarith [hδc, mul_le_mul_of_nonneg_left hVr hδ0']
    rw [if_neg hb]
    by_cases hl : E.lvl s < E.depth
    · rw [if_pos hl]
      have hcg := E.child_ne_good s (f s) hg hb hl
      have hcb := E.child_ne_bad s (f s) hg hb hl
      have hcl := E.lvl_child s (f s) hg hb hl
      have hclR : ((E.lvl (E.child s (f s)) : ℕ) : ℝ) = E.lvl s + 1 := by exact_mod_cast hcl
      by_cases h3 : reachB K E.depth s tgt = true
      · -- on the path: f descends towards tgt
        have hex : ∃ a, reachB K E.depth (E.child s a) tgt = true := by
          obtain ⟨m, hm⟩ : ∃ m, E.depth = m + 1 := ⟨E.depth - 1, by omega⟩
          have h3' : reachB K (m + 1) s tgt = true := hm ▸ h3
          rcases (reachB_succ _ _ _ _).1 h3' with h | ⟨_, a, ha⟩
          · exact absurd h hs
          · exact ⟨a, hm ▸ reachB_mono K ha⟩
        have hf : f s = hex.choose := dif_pos hex
        have hR : reachB K E.depth (E.child s (f s)) tgt = true := by
          rw [hf]; exact hex.choose_spec
        rw [hVon s hs hg hb h3]
        have := hVup' _ hcg hcb hR
        linarith
      · rw [hVoff s hs hg hb h3]
        have := hVle _ hcg hcb
        linarith
    · rw [if_neg hl, hVg, hVb]
      have h3 : ¬ reachB K E.depth s tgt = true := fun h =>
        hs (reachB_of_not_internal K (fun h' => hl h'.2.2) h)
      rw [hVoff s hs hg hb h3]
      have hle := E.lvl_le s hg hb
      have hlv : E.lvl s = E.depth := by omega
      rw [hlv]
      ring_nf
      linarith
  · by_cases h0 : src = tgt
    · rw [h0, hVt]; positivity
    by_cases h1 : src = E.good
    · rw [h1, hVg]; linarith
    by_cases h2 : src = E.bad
    · rw [h2, hVb]; linarith
    have := hVle src h1 h2
    linarith [(Nat.cast_nonneg (E.lvl src) : (0:ℝ) ≤ E.lvl src)]


/-! ## The concrete skeleton on `Fin S` -/

section concrete

/-- The concrete skeleton: state `0` is `good`, `1` is `bad`, `i + 2` is tree node `i`. -/
def ArenaFam.skelC {S A : ℕ} (hS : 3 ≤ S) (hA : 2 ≤ A) : Skel S A where
  depth := dOf A (S - 2)
  good := ⟨0, by omega⟩
  bad := ⟨1, by omega⟩
  root := ⟨2, by omega⟩
  lvl := fun s => lvlN A (S - 2) (s.val - 2)
  child := fun s a => ⟨childN A (S - 2) (s.val - 2) a.val + 2, by
    have := childN_lt' hA (n := S - 2) (by omega) (i := s.val - 2) (a := a.val) (by omega)
    omega⟩
  good_ne_bad := by simp [Fin.ext_iff]
  root_ne_good := by simp [Fin.ext_iff]
  root_ne_bad := by simp [Fin.ext_iff]
  lvl_root := by simp only; exact lvlN_zero' hA (by omega)
  lvl_le := fun s _ _ => lvlN_le' hA (by omega) _
  lvl_child := by
    intro s a _ _ hl
    simp only at hl ⊢
    rw [Nat.add_sub_cancel]
    exact lvlN_childN' hA (by omega) a.isLt hl
  child_ne_good := by intro s a _ _ _; simp [Fin.ext_iff]
  child_ne_bad := by intro s a _ _ _; simp [Fin.ext_iff]

theorem ArenaFam.skelC_depth {S A : ℕ} (hS : 3 ≤ S) (hA : 2 ≤ A) : (skelC hS hA).depth = dOf A (S - 2) := rfl
theorem ArenaFam.skelC_root {S A : ℕ} (hS : 3 ≤ S) (hA : 2 ≤ A) : (skelC hS hA).root = ⟨2, by omega⟩ := rfl
theorem ArenaFam.skelC_lvl {S A : ℕ} (hS : 3 ≤ S) (hA : 2 ≤ A) (s : Fin S) : (skelC hS hA).lvl s = lvlN A (S - 2) (s.val - 2) := rfl
theorem ArenaFam.skelC_child {S A : ℕ} (hS : 3 ≤ S) (hA : 2 ≤ A) (s : Fin S) (a : Fin A) :
    ((skelC hS hA).child s a).val = childN A (S - 2) (s.val - 2) a.val + 2 := rfl

/-- Every tree node is reachable from the root. -/
theorem ArenaFam.reach_node {S A : ℕ} (hS : 3 ≤ S) (hA : 2 ≤ A) (t : ℕ) (ht : t < S - 2) :
    reachB (skelC hS hA) (skelC hS hA).depth (skelC hS hA).root ⟨t + 2, by omega⟩ = true := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0; exact reachB_refl _ _ _
    · have hn2 : 2 ≤ S - 2 := by omega
      have hpar := parN_lt hA hn2 hpos ht
      have hpK := parN_lt_K hA hn2 hpos ht
      have hcp := childN_parN hA hn2 hpos ht
      have hK := K_lt_n hA hn2
      have h1 := ih _ hpar (by omega)
      -- the parent is an internal node
      have hint : (⟨parN A (S - 2) t + 2, by omega⟩ : Fin S) ≠ (skelC hS hA).good ∧
          (⟨parN A (S - 2) t + 2, by omega⟩ : Fin S) ≠ (skelC hS hA).bad ∧
          (skelC hS hA).lvl ⟨parN A (S - 2) t + 2, by omega⟩ < (skelC hS hA).depth := by
        refine ⟨by simp [skelC, Fin.ext_iff], by simp [skelC, Fin.ext_iff], ?_⟩
        rw [skelC_lvl hS hA, skelC_depth hS hA]
        simp only [Nat.add_sub_cancel]
        exact lvlN_lt_of_lt hA hn2 hpK
      have h2 := reachB_snoc _ h1 hint ⟨actN A (S - 2) t, actN_lt A _ (by omega) t⟩
      have h3 : (skelC hS hA).child ⟨parN A (S - 2) t + 2, by omega⟩
          ⟨actN A (S - 2) t, actN_lt A _ (by omega) t⟩ = ⟨t + 2, by omega⟩ := by
        apply Fin.ext
        rw [skelC_child hS hA]
        simp only [Nat.add_sub_cancel]
        rw [hcp]
      rw [h3] at h2
      exact reachB_depth _ h2

theorem ArenaFam.reach_all {S A : ℕ} (hS : 3 ≤ S) (hA : 2 ≤ A) (t : Fin S) (h1 : t ≠ (skelC hS hA).good) (h2 : t ≠ (skelC hS hA).bad) :
    reachB (skelC hS hA) (skelC hS hA).depth (skelC hS hA).root t = true := by
  have ht : 2 ≤ t.val := by
    by_contra h
    have : t.val = 0 ∨ t.val = 1 := by omega
    rcases this with h | h
    · exact h1 (Fin.ext h)
    · exact h2 (Fin.ext h)
  have := reach_node hS hA (t.val - 2) (by omega)
  have e : (⟨t.val - 2 + 2, by omega⟩ : Fin S) = t := Fin.ext (by simp; omega)
  rwa [e] at this

end concrete


theorem solution
    {S A : ℕ} [NeZero S] (hS : 3 ≤ S) (hA : 2 ≤ A) :
    ∃ (E₀ : LayeredArena S A)
      (Efam : ↥(countedPairs E₀.leafNat) → LayeredArena S A) (L : ℕ),
      (∀ p, E₀.good = (Efam p).good) ∧ (∀ p, E₀.bad = (Efam p).bad) ∧
      (∀ p, E₀.root = (Efam p).root) ∧ (∀ p, E₀.lvl = (Efam p).lvl) ∧
      (∀ p, E₀.depth = (Efam p).depth) ∧ (∀ p, E₀.child = (Efam p).child) ∧
      (∀ p, (Efam p).specialLeaf = p.val.1) ∧
      (∀ p, (Efam p).specialAction = p.val.2) ∧
      Fintype.card ↥(countedPairs (A := A) E₀.leafNat) = L * A ∧ 1 ≤ L ∧
      A ^ E₀.depth < A * (S - 2) ∧ S - 2 ≤ 3 * L + 1 ∧
      ∀ (δ Δ : ℝ≥0) (hδ1 : δ ≤ 1) (hΔ2 : Δ ≤ 1 / 2), (0 : ℝ) < δ → Δ ≤ 1 / 4 →
        ∀ p, mdpDiameterENN ((Efam p).toMDP hδ1 hΔ2)
          ≤ ENNReal.ofReal (4 * E₀.epiLen (δ : ℝ)) := by
  classical
  have hn1 : 1 ≤ S - 2 := by omega
  set K := skelC hS hA with hKdef
  have hreach : ∀ t : Fin S, t ≠ K.good → t ≠ K.bad → reachB K K.depth K.root t = true :=
    reach_all hS hA
  have hKlt := K_lt_n' hA hn1
  -- leaves are exactly the states with value `≥ KOf + 2`
  have hleaf : ∀ t : Fin S, t ≠ K.good → t ≠ K.bad →
      (K.lvl t = K.depth ↔ KOf A (S - 2) + 2 ≤ t.val) := by
    intro t h1 h2
    have ht : 2 ≤ t.val := by
      by_contra h
      have : t.val = 0 ∨ t.val = 1 := by omega
      rcases this with h | h
      · exact h1 (Fin.ext h)
      · exact h2 (Fin.ext h)
    rw [skelC_lvl hS hA, skelC_depth hS hA, lvlN_eq_d_iff' hA hn1]
    omega
  have hgood : ∀ t : Fin S, t ≠ K.good ↔ t.val ≠ 0 := fun t => not_congr Fin.ext_iff
  have hbad : ∀ t : Fin S, t ≠ K.bad ↔ t.val ≠ 1 := fun t => not_congr Fin.ext_iff
  -- the special leaf of the base arena: the last node
  let spec₀ : Fin S := ⟨S - 1, by omega⟩
  have hs0g : spec₀ ≠ K.good := (hgood _).2 (show S - 1 ≠ 0 by omega)
  have hs0b : spec₀ ≠ K.bad := (hbad _).2 (show S - 1 ≠ 1 by omega)
  have hs0l : K.lvl spec₀ = K.depth :=
    (hleaf _ hs0g hs0b).2 (show KOf A (S - 2) + 2 ≤ S - 1 by omega)
  let E₀ : LayeredArena S A :=
    mkArena K spec₀ ⟨0, by omega⟩ ⟨0, by omega⟩ hs0g hs0b hs0l (hreach _ hs0g hs0b)
  have hcp : ∀ p : ↥(countedPairs (A := A) E₀.leafNat),
      p.val.1 ≠ K.good ∧ p.val.1 ≠ K.bad ∧ K.lvl p.val.1 = K.depth := by
    intro p
    have hp := (mem_countedPairs).1 p.property
    unfold leafNat at hp
    split_ifs at hp with h
    exact h
  let Efam : ↥(countedPairs (A := A) E₀.leafNat) → LayeredArena S A := fun p =>
    mkArena K p.val.1 p.val.2 ⟨0, by omega⟩ (hcp p).1 (hcp p).2.1 (hcp p).2.2
      (hreach _ (hcp p).1 (hcp p).2.1)
  refine ⟨E₀, Efam, S - 2 - KOf A (S - 2), fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- cardinality of the counted pairs
    rw [Fintype.card_coe]
    have hprod : countedPairs (A := A) E₀.leafNat =
        (Finset.univ.filter fun s : Fin S => E₀.leafNat s = 1) ×ˢ Finset.univ := by
      ext ⟨s, a⟩; simp [countedPairs]
    rw [hprod, Finset.card_product, Finset.card_univ, Fintype.card_fin]
    congr 1
    have hfilt : (Finset.univ.filter fun s : Fin S => E₀.leafNat s = 1) =
        Finset.Ici (⟨KOf A (S - 2) + 2, by omega⟩ : Fin S) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, Fin.le_def]
      unfold leafNat
      constructor
      · intro h
        split_ifs at h with h'
        exact (hleaf s h'.1 h'.2.1).1 h'.2.2
      · intro h
        have h1 : s ≠ E₀.good := (hgood s).2 (by omega)
        have h2 : s ≠ E₀.bad := (hbad s).2 (by omega)
        rw [if_pos ⟨h1, h2, (hleaf s h1 h2).2 h⟩]
    rw [hfilt, Fin.card_Ici]
    simp only
    omega
  · omega
  · exact pow_d_lt' hA hn1
  · exact n_le_three_L' hA hn1
  · intro δ Δ hδ1 hΔ2 hδ0 hΔ4 p
    exact diameter_le (Efam p) hδ1 hΔ2 hδ0 hΔ4 (fun t h1 h2 => hreach t h1 h2)
