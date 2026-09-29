-- Prove2me | solution 1 for MetricTSP.three_paths_opt_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-24T20:50:53.354776+00:00
-- url     : https://prove2.me/submissions/aaf88157-ba6c-48f4-9880-1684eb5f3bbd

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths

set_option maxHeartbeats 1600000

namespace MetricTSP

open Finset

variable {k : ℕ}

lemma nat_dist_def' (a b : ℕ) : Nat.dist a b = (a - b) + (b - a) := rfl

/-! ### Coordinate facts (as in the sibling files) -/

lemma tpSpec3 (hk : 1 ≤ k) (v : Fin (3*k+2)) :
    (tpPath k v = 3 ∧ (tpPos k v = 0 ∨ tpPos k v = k+1))
    ∨ (tpPath k v < 3 ∧ 1 ≤ tpPos k v ∧ tpPos k v ≤ k) := by
  have hv := v.isLt
  unfold tpPath tpPos
  by_cases h : v.val = 0 ∨ v.val = 3*k+1
  · rw [if_pos h]
    left
    rcases h with h | h <;> rw [h] <;> simp <;> omega
  · rw [if_neg h]
    right
    push_neg at h
    have hmod : (v.val - 1) % k < k := Nat.mod_lt _ (by omega)
    have hdivlt : (v.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    rw [if_neg h.1, if_neg h.2]
    omega

lemma tpCoord_inj3 (hk : 1 ≤ k) (u v : Fin (3*k+2))
    (hp : tpPath k u = tpPath k v) (hq : tpPos k u = tpPos k v) : u = v := by
  have hu := u.isLt
  have hv := v.isLt
  apply Fin.ext
  unfold tpPath at hp
  unfold tpPos at hq
  by_cases h1 : u.val = 0 ∨ u.val = 3*k+1 <;> by_cases h2 : v.val = 0 ∨ v.val = 3*k+1
  · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · rw [h1, h2]
    · exfalso
      rw [h1, h2] at hq
      rw [if_pos rfl] at hq
      rw [if_neg (by omega), if_pos rfl] at hq
      omega
    · exfalso
      rw [h1, h2] at hq
      rw [if_neg (by omega), if_pos rfl, if_pos rfl] at hq
      omega
    · rw [h1, h2]
  · rw [if_pos h1, if_neg h2] at hp
    push_neg at h2
    have hdivlt : (v.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega
  · rw [if_neg h1, if_pos h2] at hp
    push_neg at h1
    have hdivlt : (u.val - 1) / k < 3 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      omega
    omega
  · push_neg at h1 h2
    rw [if_neg h1.1, if_neg h1.2] at hq
    rw [if_neg h2.1, if_neg h2.2] at hq
    rw [if_neg (not_or.mpr h1), if_neg (not_or.mpr h2)] at hp
    have e1 : k * ((u.val - 1) / k) + (u.val - 1) % k = u.val - 1 := Nat.div_add_mod _ k
    have e2 : k * ((v.val - 1) / k) + (v.val - 1) % k = v.val - 1 := Nat.div_add_mod _ k
    rw [hp] at e1
    have e3 : (u.val - 1) % k = (v.val - 1) % k := by omega
    rw [e3] at e1
    omega

/-! ### The edge-usage count of a single step -/

/-- How many times the canonical shortest route of a step between coordinate
pairs `(Pu, pu)` and `(Pv, pv)` uses the level-`ℓ` edge of path `j`. Shared-path
steps route directly; cross-path steps route through the nearer hub. -/
def cntVal (k Pu pu Pv pv j ℓ : ℕ) : ℕ :=
  if Pu = 3 ∨ Pv = 3 ∨ Pu = Pv then
    if j = (if Pu ≠ 3 then Pu else if Pv ≠ 3 then Pv else 0)
        ∧ min pu pv ≤ ℓ ∧ ℓ < max pu pv then 1 else 0
  else
    if pu + pv ≤ 2*(k+1) - (pu + pv) then
      if (j = Pu ∧ ℓ < pu) ∨ (j = Pv ∧ ℓ < pv) then 1 else 0
    else
      if (j = Pu ∧ pu ≤ ℓ) ∨ (j = Pv ∧ pv ≤ ℓ) then 1 else 0

/-- Usage count of a step of the tour. -/
def stepCnt (k : ℕ) (u v : Fin (3*k+2)) (j ℓ : ℕ) : ℕ :=
  cntVal k (tpPath k u) (tpPos k u) (tpPath k v) (tpPos k v) j ℓ

/-! ### Interval counting -/

lemma count_band (N a b : ℕ) (hb : b ≤ N) :
    ∑ ℓ ∈ Finset.range N, (if a ≤ ℓ ∧ ℓ < b then (1:ℕ) else 0) = b - a := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_const, smul_eq_mul, mul_one]
  have hset : (Finset.range N).filter (fun ℓ => a ≤ ℓ ∧ ℓ < b) = Finset.Ico a b := by
    ext ℓ
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, Nat.card_Ico]

lemma count_lt (N b : ℕ) (hb : b ≤ N) :
    ∑ ℓ ∈ Finset.range N, (if ℓ < b then (1:ℕ) else 0) = b := by
  have h := count_band N 0 b hb
  calc ∑ ℓ ∈ Finset.range N, (if ℓ < b then (1:ℕ) else 0)
      = ∑ ℓ ∈ Finset.range N, (if 0 ≤ ℓ ∧ ℓ < b then (1:ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro ℓ _
        congr 1
        simp
    _ = b - 0 := h
    _ = b := by omega

lemma count_ge (N a : ℕ) (ha : a ≤ N) :
    ∑ ℓ ∈ Finset.range N, (if a ≤ ℓ then (1:ℕ) else 0) = N - a := by
  have h := count_band N a N le_rfl
  calc ∑ ℓ ∈ Finset.range N, (if a ≤ ℓ then (1:ℕ) else 0)
      = ∑ ℓ ∈ Finset.range N, (if a ≤ ℓ ∧ ℓ < N then (1:ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        rw [Finset.mem_range] at hℓ
        congr 1
        simp [hℓ]
    _ = N - a := h

/-! ### The cost identity -/

/-- Total usage of a step over all edges equals its metric length. -/
lemma cntVal_total (hk : 1 ≤ k) {Pu pu Pv pv : ℕ}
    (hu : (Pu = 3 ∧ (pu = 0 ∨ pu = k+1)) ∨ (Pu < 3 ∧ 1 ≤ pu ∧ pu ≤ k))
    (hv : (Pv = 3 ∧ (pv = 0 ∨ pv = k+1)) ∨ (Pv < 3 ∧ 1 ≤ pv ∧ pv ≤ k)) :
    ∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1), cntVal k Pu pu Pv pv j ℓ
      = (if Pu = 3 ∨ Pv = 3 ∨ Pu = Pv then Nat.dist pu pv
         else min (pu + pv) (2*(k+1) - (pu + pv))) := by
  by_cases hsh : Pu = 3 ∨ Pv = 3 ∨ Pu = Pv
  · rw [if_pos hsh]
    set tgt : ℕ := (if Pu ≠ 3 then Pu else if Pv ≠ 3 then Pv else 0) with htgt
    have htgt3 : tgt < 3 := by
      rw [htgt]
      split_ifs <;> omega
    have hstep : ∀ j ℓ : ℕ, cntVal k Pu pu Pv pv j ℓ
        = if j = tgt then (if min pu pv ≤ ℓ ∧ ℓ < max pu pv then 1 else 0) else 0 := by
      intro j ℓ
      unfold cntVal
      rw [if_pos hsh, ← htgt]
      by_cases hj : j = tgt
      · simp [hj]
      · simp [hj]
    calc ∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1), cntVal k Pu pu Pv pv j ℓ
        = ∑ j ∈ Finset.range 3, (if j = tgt then
            (∑ ℓ ∈ Finset.range (k+1), (if min pu pv ≤ ℓ ∧ ℓ < max pu pv then (1:ℕ) else 0))
            else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_congr rfl (fun ℓ _ => hstep j ℓ)]
          by_cases hj : j = tgt
          · simp [hj]
          · simp [hj]
      _ = ∑ ℓ ∈ Finset.range (k+1), (if min pu pv ≤ ℓ ∧ ℓ < max pu pv then (1:ℕ) else 0) := by
          rw [Finset.sum_ite_eq' (Finset.range 3) tgt]
          rw [if_pos (Finset.mem_range.mpr htgt3)]
      _ = max pu pv - min pu pv := by
          apply count_band
          omega
      _ = Nat.dist pu pv := by
          rw [nat_dist_def']
          omega
  · rw [if_neg hsh]
    push_neg at hsh
    obtain ⟨hPu3, hPv3, hPuv⟩ := hsh
    have hvu : Pv ≠ Pu := fun h => hPuv h.symm
    have hPu : Pu < 3 := by omega
    have hPv : Pv < 3 := by omega
    have hpu : 1 ≤ pu ∧ pu ≤ k := by omega
    have hpv : 1 ≤ pv ∧ pv ≤ k := by omega
    by_cases hroute : pu + pv ≤ 2*(k+1) - (pu + pv)
    · have hstep : ∀ j ℓ : ℕ, cntVal k Pu pu Pv pv j ℓ
          = (if j = Pu then (if ℓ < pu then 1 else 0) else 0)
            + (if j = Pv then (if ℓ < pv then 1 else 0) else 0) := by
        intro j ℓ
        unfold cntVal
        rw [if_neg (by omega), if_pos hroute]
        by_cases hj1 : j = Pu <;> by_cases hj2 : j = Pv
        · omega
        · simp [hj1, hPuv]
        · simp [hj2, hvu]
        · simp [hj1, hj2]
      calc ∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1), cntVal k Pu pu Pv pv j ℓ
          = ∑ j ∈ Finset.range 3,
              ((if j = Pu then (∑ ℓ ∈ Finset.range (k+1), (if ℓ < pu then (1:ℕ) else 0)) else 0)
              + (if j = Pv then (∑ ℓ ∈ Finset.range (k+1), (if ℓ < pv then (1:ℕ) else 0)) else 0)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_congr rfl (fun ℓ _ => hstep j ℓ), Finset.sum_add_distrib]
            congr 1
            · by_cases hj : j = Pu <;> simp [hj]
            · by_cases hj : j = Pv <;> simp [hj]
        _ = pu + pv := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range 3) Pu,
              Finset.sum_ite_eq' (Finset.range 3) Pv,
              if_pos (Finset.mem_range.mpr hPu), if_pos (Finset.mem_range.mpr hPv),
              count_lt (k+1) pu (by omega), count_lt (k+1) pv (by omega)]
        _ = min (pu + pv) (2*(k+1) - (pu + pv)) := by omega
    · have hstep : ∀ j ℓ : ℕ, cntVal k Pu pu Pv pv j ℓ
          = (if j = Pu then (if pu ≤ ℓ then 1 else 0) else 0)
            + (if j = Pv then (if pv ≤ ℓ then 1 else 0) else 0) := by
        intro j ℓ
        unfold cntVal
        rw [if_neg (by omega), if_neg hroute]
        by_cases hj1 : j = Pu <;> by_cases hj2 : j = Pv
        · omega
        · simp [hj1, hPuv]
        · simp [hj2, hvu]
        · simp [hj1, hj2]
      calc ∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1), cntVal k Pu pu Pv pv j ℓ
          = ∑ j ∈ Finset.range 3,
              ((if j = Pu then (∑ ℓ ∈ Finset.range (k+1), (if pu ≤ ℓ then (1:ℕ) else 0)) else 0)
              + (if j = Pv then (∑ ℓ ∈ Finset.range (k+1), (if pv ≤ ℓ then (1:ℕ) else 0)) else 0)) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_congr rfl (fun ℓ _ => hstep j ℓ), Finset.sum_add_distrib]
            congr 1
            · by_cases hj : j = Pu <;> simp [hj]
            · by_cases hj : j = Pv <;> simp [hj]
        _ = (k+1-pu) + (k+1-pv) := by
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range 3) Pu,
              Finset.sum_ite_eq' (Finset.range 3) Pv,
              if_pos (Finset.mem_range.mpr hPu), if_pos (Finset.mem_range.mpr hPv),
              count_ge (k+1) pu (by omega), count_ge (k+1) pv (by omega)]
        _ = min (pu + pv) (2*(k+1) - (pu + pv)) := by omega

/-- The metric length of a step is the total edge usage of its route. -/
lemma stepCnt_total (hk : 1 ≤ k) (u v : Fin (3*k+2)) :
    tpDist k u v = ∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1), stepCnt k u v j ℓ := by
  have hu := tpSpec3 hk u
  have hv := tpSpec3 hk v
  have h := cntVal_total hk hu hv
  unfold stepCnt
  rw [h]
  rfl


/-! ### Parity, incidence, and straddling of step counts -/

lemma cntVal_vertex (hk : 1 ≤ k) {Pu pu Pv pv jw mw : ℕ}
    (hu : (Pu = 3 ∧ (pu = 0 ∨ pu = k+1)) ∨ (Pu < 3 ∧ 1 ≤ pu ∧ pu ≤ k))
    (hv : (Pv = 3 ∧ (pv = 0 ∨ pv = k+1)) ∨ (Pv < 3 ∧ 1 ≤ pv ∧ pv ≤ k))
    (hjw : jw < 3) (hmw1 : 1 ≤ mw) (hmwk : mw ≤ k) :
    (cntVal k Pu pu Pv pv jw (mw-1) + cntVal k Pu pu Pv pv jw mw) % 2
      = ((if Pu = jw ∧ pu = mw then 1 else 0)
        + (if Pv = jw ∧ pv = mw then 1 else 0)) % 2 := by
  unfold cntVal
  split_ifs <;> omega

lemma cntVal_vertex_pos (hk : 1 ≤ k) {Pu pu Pv pv jw mw : ℕ}
    (hu : (Pu = 3 ∧ (pu = 0 ∨ pu = k+1)) ∨ (Pu < 3 ∧ 1 ≤ pu ∧ pu ≤ k))
    (hv : (Pv = 3 ∧ (pv = 0 ∨ pv = k+1)) ∨ (Pv < 3 ∧ 1 ≤ pv ∧ pv ≤ k))
    (hjw : jw < 3) (hmw1 : 1 ≤ mw) (hmwk : mw ≤ k)
    (hne : ¬(Pu = Pv ∧ pu = pv))
    (hw : (Pu = jw ∧ pu = mw) ∨ (Pv = jw ∧ pv = mw)) :
    1 ≤ cntVal k Pu pu Pv pv jw (mw-1) + cntVal k Pu pu Pv pv jw mw := by
  unfold cntVal
  split_ifs <;> omega

lemma cntVal_hub_s (hk : 1 ≤ k) {Pu pu Pv pv : ℕ}
    (hu : (Pu = 3 ∧ (pu = 0 ∨ pu = k+1)) ∨ (Pu < 3 ∧ 1 ≤ pu ∧ pu ≤ k))
    (hv : (Pv = 3 ∧ (pv = 0 ∨ pv = k+1)) ∨ (Pv < 3 ∧ 1 ≤ pv ∧ pv ≤ k)) :
    (cntVal k Pu pu Pv pv 0 0 + cntVal k Pu pu Pv pv 1 0 + cntVal k Pu pu Pv pv 2 0) % 2
      = ((if pu = 0 then 1 else 0) + (if pv = 0 then 1 else 0)) % 2 := by
  unfold cntVal
  split_ifs <;> omega

lemma cntVal_straddle (hk : 1 ≤ k) {Pu pu Pv pv j ℓ1 ℓ2 : ℕ}
    (hu : (Pu = 3 ∧ (pu = 0 ∨ pu = k+1)) ∨ (Pu < 3 ∧ 1 ≤ pu ∧ pu ≤ k))
    (hv : (Pv = 3 ∧ (pv = 0 ∨ pv = k+1)) ∨ (Pv < 3 ∧ 1 ≤ pv ∧ pv ≤ k))
    (hj : j < 3) (h12 : ℓ1 < ℓ2) (hl2 : ℓ2 ≤ k)
    (hin : Pu = j ∧ ℓ1 + 1 ≤ pu ∧ pu ≤ ℓ2)
    (hout : ¬(Pv = j ∧ ℓ1 + 1 ≤ pv ∧ pv ≤ ℓ2)) :
    1 ≤ cntVal k Pu pu Pv pv j ℓ1 + cntVal k Pu pu Pv pv j ℓ2 := by
  unfold cntVal
  split_ifs <;> omega

/-! ### Tour-level machinery -/

lemma rot_val3 {m : ℕ} (i : Fin m) : (finRotate m i).val = (i.val + 1) % m := by
  have : NeZero m := ⟨Nat.pos_iff_ne_zero.mp i.pos⟩
  rw [finRotate_apply, Fin.add_def, Fin.val_one']
  conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

lemma rot_ne3 {m : ℕ} (hm : 2 ≤ m) (i : Fin m) : finRotate m i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  rw [rot_val3] at hv
  have hlt := i.isLt
  rcases Nat.lt_or_ge (i.val + 1) m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1] at hv
    omega
  · have he : i.val + 1 = m := by omega
    rw [he, Nat.mod_self] at hv
    omega

lemma exists_exit3 {m : ℕ} (hm : 2 ≤ m) (T : Finset (Fin m)) (hT : T.Nonempty)
    (hTu : T ≠ univ) : ∃ i ∈ T, finRotate m i ∉ T := by
  by_contra hcon
  push_neg at hcon
  apply hTu
  obtain ⟨a, ha⟩ := hT
  have hcyc := isCycle_finRotate_of_le hm
  have key : ∀ c : ℕ, ((finRotate m) ^ c) a ∈ T := by
    intro c
    induction c with
    | zero => simpa using ha
    | succ c ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hcon _ ih
  apply Finset.eq_univ_iff_forall.mpr
  intro j
  have hsc := hcyc.sameCycle (rot_ne3 hm a) (rot_ne3 hm j)
  obtain ⟨c, _, hc⟩ := hsc.exists_pow_eq'
  exact hc ▸ key c

/-- Construction of the internal city with given coordinates. -/
lemma tpMk (hk : 1 ≤ k) {p i : ℕ} (hp : p < 3) (hi1 : 1 ≤ i) (hik : i ≤ k) :
    ∃ w : Fin (3*k+2), tpPath k w = p ∧ tpPos k w = i := by
  have hpk : p * k ≤ 2 * k := Nat.mul_le_mul_right k (by omega)
  refine ⟨⟨1 + p*k + (i-1), by omega⟩, ?_, ?_⟩
  · unfold tpPath
    rw [if_neg (by simp only [Fin.val_mk]; omega)]
    simp only [Fin.val_mk]
    have h1 : 1 + p*k + (i-1) - 1 = p*k + (i-1) := by omega
    rw [h1, Nat.mul_comm p k, Nat.mul_add_div (by omega), Nat.div_eq_of_lt (by omega)]
    omega
  · unfold tpPos
    rw [if_neg (by simp only [Fin.val_mk]; omega), if_neg (by simp only [Fin.val_mk]; omega)]
    simp only [Fin.val_mk]
    have h1 : 1 + p*k + (i-1) - 1 = p*k + (i-1) := by omega
    rw [h1, Nat.mul_comm p k, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The total usage of the level-`ℓ` edge of path `j` by the tour `π`. -/
def xUse (k : ℕ) (π : Equiv.Perm (Fin (3*k+2))) (j ℓ : ℕ) : ℕ :=
  ∑ i : Fin (3*k+2), stepCnt k (π i) (π (finRotate (3*k+2) i)) j ℓ

lemma spec_pack (hk : 1 ≤ k) (v : Fin (3*k+2)) :
    (tpPath k v = 3 ∧ (tpPos k v = 0 ∨ tpPos k v = k+1))
    ∨ (tpPath k v < 3 ∧ 1 ≤ tpPos k v ∧ tpPos k v ≤ k) := tpSpec3 hk v

/-- The tour cost equals the total edge usage. -/
lemma tour_cost_eq (hk : 1 ≤ k) (π : Equiv.Perm (Fin (3*k+2))) :
    tourCost (tpCost k) π
      = ((∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1), xUse k π j ℓ : ℕ) : ℝ) := by
  unfold tourCost tpCost
  rw [← Nat.cast_sum]
  congr 1
  calc ∑ i : Fin (3*k+2), tpDist k (π i) (π (finRotate (3*k+2) i))
      = ∑ i : Fin (3*k+2), ∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1),
          stepCnt k (π i) (π (finRotate (3*k+2) i)) j ℓ :=
        Finset.sum_congr rfl (fun i _ => stepCnt_total hk _ _)
    _ = ∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1), xUse k π j ℓ := by
        unfold xUse
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]

/-- Each city is the source of exactly one step and the target of exactly one. -/
lemma endpoint_count (hk : 1 ≤ k) (π : Equiv.Perm (Fin (3*k+2))) (w : Fin (3*k+2)) :
    ∑ i : Fin (3*k+2), ((if π i = w then (1:ℕ) else 0)
      + (if π (finRotate (3*k+2) i) = w then (1:ℕ) else 0)) = 2 := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ i : Fin (3*k+2), (if π i = w then (1:ℕ) else 0) = 1 := by
    have hpred : ∀ i : Fin (3*k+2), (π i = w) ↔ (i = π.symm w) := fun i => by
      constructor
      · intro h
        rw [← h]
        simp
      · intro h
        rw [h]
        simp
    rw [Finset.sum_congr rfl fun i _ => if_congr (hpred i) rfl rfl]
    simp
  have h2 : ∑ i : Fin (3*k+2), (if π (finRotate (3*k+2) i) = w then (1:ℕ) else 0) = 1 := by
    have hpred : ∀ i : Fin (3*k+2), (π (finRotate (3*k+2) i) = w) ↔
        (i = (finRotate (3*k+2)).symm (π.symm w)) := fun i => by
      constructor
      · intro h
        apply (finRotate (3*k+2)).injective
        rw [Equiv.apply_symm_apply]
        apply π.injective
        rw [Equiv.apply_symm_apply, h]
      · intro h
        rw [h, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [Finset.sum_congr rfl fun i _ => if_congr (hpred i) rfl rfl]
    simp
  omega

/-- Steps have distinct endpoints. -/
lemma step_ne (hk : 1 ≤ k) (π : Equiv.Perm (Fin (3*k+2))) (i : Fin (3*k+2)) :
    π i ≠ π (finRotate (3*k+2) i) := by
  intro h
  exact rot_ne3 (by omega) i (π.injective h.symm)


/-- Parity of usages around an internal city. -/
lemma xUse_vertex_parity (hk : 1 ≤ k) (π : Equiv.Perm (Fin (3*k+2))) {jw mw : ℕ}
    (hjw : jw < 3) (hmw1 : 1 ≤ mw) (hmwk : mw ≤ k) :
    (xUse k π jw (mw-1) + xUse k π jw mw) % 2 = 0 := by
  obtain ⟨w, hwp, hwq⟩ := tpMk hk hjw hmw1 hmwk
  have hstep : ∀ i : Fin (3*k+2),
      (stepCnt k (π i) (π (finRotate (3*k+2) i)) jw (mw-1)
        + stepCnt k (π i) (π (finRotate (3*k+2) i)) jw mw) % 2
      = ((if π i = w then (1:ℕ) else 0)
        + (if π (finRotate (3*k+2) i) = w then (1:ℕ) else 0)) % 2 := by
    intro i
    have hcoord : ∀ z : Fin (3*k+2), (tpPath k z = jw ∧ tpPos k z = mw) ↔ z = w := by
      intro z
      constructor
      · rintro ⟨h1, h2⟩
        exact tpCoord_inj3 hk z w (h1.trans hwp.symm) (h2.trans hwq.symm)
      · rintro rfl
        exact ⟨hwp, hwq⟩
    unfold stepCnt
    rw [cntVal_vertex hk (spec_pack hk _) (spec_pack hk _) hjw hmw1 hmwk]
    rw [if_congr (hcoord (π i)) rfl rfl,
      if_congr (hcoord (π (finRotate (3*k+2) i))) rfl rfl]
  have hsum : (xUse k π jw (mw-1) + xUse k π jw mw) % 2
      = (∑ i : Fin (3*k+2), ((if π i = w then (1:ℕ) else 0)
        + (if π (finRotate (3*k+2) i) = w then (1:ℕ) else 0))) % 2 := by
    unfold xUse
    rw [← Finset.sum_add_distrib, Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => hstep i)
  rw [hsum, endpoint_count hk π w]

/-- Positivity of usages around an internal city. -/
lemma xUse_vertex_pos (hk : 1 ≤ k) (π : Equiv.Perm (Fin (3*k+2))) {jw mw : ℕ}
    (hjw : jw < 3) (hmw1 : 1 ≤ mw) (hmwk : mw ≤ k) :
    1 ≤ xUse k π jw (mw-1) + xUse k π jw mw := by
  obtain ⟨w, hwp, hwq⟩ := tpMk hk hjw hmw1 hmwk
  set i0 := π.symm w with hi0
  have hw0 : π i0 = w := by
    rw [hi0]
    simp
  have hne : ¬(tpPath k (π i0) = tpPath k (π (finRotate (3*k+2) i0)) ∧
      tpPos k (π i0) = tpPos k (π (finRotate (3*k+2) i0))) := by
    rintro ⟨h1, h2⟩
    exact step_ne hk π i0 (tpCoord_inj3 hk _ _ h1 h2)
  have hstep : 1 ≤ stepCnt k (π i0) (π (finRotate (3*k+2) i0)) jw (mw-1)
      + stepCnt k (π i0) (π (finRotate (3*k+2) i0)) jw mw := by
    unfold stepCnt
    apply cntVal_vertex_pos hk (spec_pack hk _) (spec_pack hk _) hjw hmw1 hmwk hne
    left
    rw [hw0, hwp, hwq]
    exact ⟨rfl, rfl⟩
  calc 1 ≤ stepCnt k (π i0) (π (finRotate (3*k+2) i0)) jw (mw-1)
        + stepCnt k (π i0) (π (finRotate (3*k+2) i0)) jw mw := hstep
    _ ≤ xUse k π jw (mw-1) + xUse k π jw mw := by
        unfold xUse
        apply Nat.add_le_add
        · exact Finset.single_le_sum
            (f := fun i => stepCnt k (π i) (π (finRotate (3*k+2) i)) jw (mw-1))
            (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)
        · exact Finset.single_le_sum
            (f := fun i => stepCnt k (π i) (π (finRotate (3*k+2) i)) jw mw)
            (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)

/-- The unique city at position zero is `s`. -/
lemma pos_zero_iff (hk : 1 ≤ k) (z : Fin (3*k+2)) :
    tpPos k z = 0 ↔ z.val = 0 := by
  constructor
  · intro h
    unfold tpPos at h
    by_cases h0 : z.val = 0
    · exact h0
    · rw [if_neg h0] at h
      by_cases hT : z.val = 3*k+1
      · rw [if_pos hT] at h
        omega
      · rw [if_neg hT] at h
        omega
  · intro h
    unfold tpPos
    rw [if_pos h]

/-- Parity of the three level-zero usages. -/
lemma xUse_hub_parity (hk : 1 ≤ k) (π : Equiv.Perm (Fin (3*k+2))) :
    (xUse k π 0 0 + xUse k π 1 0 + xUse k π 2 0) % 2 = 0 := by
  set w : Fin (3*k+2) := ⟨0, by omega⟩ with hw
  have hcoord : ∀ z : Fin (3*k+2), (tpPos k z = 0) ↔ z = w := by
    intro z
    rw [pos_zero_iff hk]
    constructor
    · intro h
      apply Fin.ext
      exact h
    · rintro rfl
      rfl
  have hstep : ∀ i : Fin (3*k+2),
      (stepCnt k (π i) (π (finRotate (3*k+2) i)) 0 0
        + stepCnt k (π i) (π (finRotate (3*k+2) i)) 1 0
        + stepCnt k (π i) (π (finRotate (3*k+2) i)) 2 0) % 2
      = ((if π i = w then (1:ℕ) else 0)
        + (if π (finRotate (3*k+2) i) = w then (1:ℕ) else 0)) % 2 := by
    intro i
    unfold stepCnt
    rw [cntVal_hub_s hk (spec_pack hk _) (spec_pack hk _)]
    rw [if_congr (hcoord (π i)) rfl rfl,
      if_congr (hcoord (π (finRotate (3*k+2) i))) rfl rfl]
  have hsum : (xUse k π 0 0 + xUse k π 1 0 + xUse k π 2 0) % 2
      = (∑ i : Fin (3*k+2), ((if π i = w then (1:ℕ) else 0)
        + (if π (finRotate (3*k+2) i) = w then (1:ℕ) else 0))) % 2 := by
    unfold xUse
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_nat_mod]
    conv_rhs => rw [Finset.sum_nat_mod]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => hstep i)
  rw [hsum, endpoint_count hk π w]

/-- No path can have two unused edges. -/
lemma xUse_no_two_zeros (hk : 1 ≤ k) (π : Equiv.Perm (Fin (3*k+2))) {j ℓ1 ℓ2 : ℕ}
    (hj : j < 3) (h12 : ℓ1 < ℓ2) (hl2 : ℓ2 ≤ k)
    (hz1 : xUse k π j ℓ1 = 0) (hz2 : xUse k π j ℓ2 = 0) : False := by
  classical
  obtain ⟨w, hwp, hwq⟩ := tpMk hk hj (i := ℓ1+1) (by omega) (by omega)
  set T : Finset (Fin (3*k+2)) := univ.filter
    (fun i => tpPath k (π i) = j ∧ ℓ1+1 ≤ tpPos k (π i) ∧ tpPos k (π i) ≤ ℓ2) with hT
  have hTne : T.Nonempty := by
    refine ⟨π.symm w, ?_⟩
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have : π (π.symm w) = w := by simp
    rw [this, hwp, hwq]
    omega
  have hTu : T ≠ univ := by
    intro hcontra
    have hmem : π.symm ⟨0, by omega⟩ ∈ T := hcontra ▸ Finset.mem_univ _
    rw [hT, Finset.mem_filter] at hmem
    have : π (π.symm (⟨0, by omega⟩ : Fin (3*k+2))) = ⟨0, by omega⟩ := by simp
    rw [this] at hmem
    have hp0 : tpPos k (⟨0, by omega⟩ : Fin (3*k+2)) = 0 := by
      unfold tpPos
      rw [if_pos rfl]
    omega
  obtain ⟨i, hiT, hiT'⟩ := exists_exit3 (by omega) T hTne hTu
  rw [hT, Finset.mem_filter] at hiT hiT'
  have hin : tpPath k (π i) = j ∧ ℓ1+1 ≤ tpPos k (π i) ∧ tpPos k (π i) ≤ ℓ2 := hiT.2
  have hout : ¬(tpPath k (π (finRotate (3*k+2) i)) = j ∧
      ℓ1+1 ≤ tpPos k (π (finRotate (3*k+2) i)) ∧
      tpPos k (π (finRotate (3*k+2) i)) ≤ ℓ2) := by
    intro hc
    exact hiT' ⟨Finset.mem_univ _, hc⟩
  have hone : 1 ≤ stepCnt k (π i) (π (finRotate (3*k+2) i)) j ℓ1
      + stepCnt k (π i) (π (finRotate (3*k+2) i)) j ℓ2 := by
    unfold stepCnt
    exact cntVal_straddle hk (spec_pack hk _) (spec_pack hk _) hj h12 hl2 hin hout
  have hle : stepCnt k (π i) (π (finRotate (3*k+2) i)) j ℓ1
      + stepCnt k (π i) (π (finRotate (3*k+2) i)) j ℓ2
      ≤ xUse k π j ℓ1 + xUse k π j ℓ2 := by
    unfold xUse
    apply Nat.add_le_add
    · exact Finset.single_le_sum
        (f := fun a => stepCnt k (π a) (π (finRotate (3*k+2) a)) j ℓ1)
        (fun a _ => Nat.zero_le _) (Finset.mem_univ i)
    · exact Finset.single_le_sum
        (f := fun a => stepCnt k (π a) (π (finRotate (3*k+2) a)) j ℓ2)
        (fun a _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- Along each path, all usage parities agree. -/
lemma xUse_parity_const (hk : 1 ≤ k) (π : Equiv.Perm (Fin (3*k+2))) {j : ℕ} (hj : j < 3) :
    ∀ ℓ, ℓ ≤ k → xUse k π j ℓ % 2 = xUse k π j 0 % 2 := by
  intro ℓ
  induction ℓ with
  | zero => intro _; rfl
  | succ m ih =>
      intro hm
      have hpar := xUse_vertex_parity hk π hj (mw := m+1) (by omega) hm
      have hih := ih (by omega)
      have hm1 : m + 1 - 1 = m := by omega
      rw [hm1] at hpar
      omega

/-- The per-path usage totals. -/
lemma path_total (hk : 1 ≤ k) (π : Equiv.Perm (Fin (3*k+2))) {j : ℕ} (hj : j < 3) :
    (xUse k π j 0 % 2 = 1 → k+1 ≤ ∑ ℓ ∈ Finset.range (k+1), xUse k π j ℓ)
    ∧ (xUse k π j 0 % 2 = 0 → 2*k ≤ ∑ ℓ ∈ Finset.range (k+1), xUse k π j ℓ) := by
  classical
  constructor
  · intro hodd
    have hone : ∀ ℓ ∈ Finset.range (k+1), 1 ≤ xUse k π j ℓ := by
      intro ℓ hℓ
      rw [Finset.mem_range] at hℓ
      have := xUse_parity_const hk π hj ℓ (by omega)
      omega
    calc k+1 = (Finset.range (k+1)).card • 1 := by
          rw [Finset.card_range, smul_eq_mul, mul_one]
      _ ≤ ∑ ℓ ∈ Finset.range (k+1), xUse k π j ℓ :=
          Finset.card_nsmul_le_sum _ _ _ hone
  · intro heven
    have hZ1 : ((Finset.range (k+1)).filter (fun ℓ => xUse k π j ℓ = 0)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter, Finset.mem_range] at ha hb
      by_contra hab
      rcases Nat.lt_or_ge a b with h | h
      · exact xUse_no_two_zeros hk π hj h (by omega) ha.2 hb.2
      · have hba : b < a := by omega
        exact xUse_no_two_zeros hk π hj hba (by omega) hb.2 ha.2
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (k+1))
      (fun ℓ => xUse k π j ℓ = 0) (fun ℓ => xUse k π j ℓ)
    have hcards := Finset.filter_card_add_filter_neg_card_eq_card
      (s := Finset.range (k+1)) (p := fun ℓ => xUse k π j ℓ = 0)
    rw [Finset.card_range] at hcards
    have hzero : ∑ ℓ ∈ (Finset.range (k+1)).filter (fun ℓ => xUse k π j ℓ = 0),
        xUse k π j ℓ = 0 := by
      apply Finset.sum_eq_zero
      intro ℓ hℓ
      rw [Finset.mem_filter] at hℓ
      exact hℓ.2
    have htwo : ((Finset.range (k+1)).filter (fun ℓ => ¬xUse k π j ℓ = 0)).card • 2
        ≤ ∑ ℓ ∈ (Finset.range (k+1)).filter (fun ℓ => ¬xUse k π j ℓ = 0), xUse k π j ℓ := by
      apply Finset.card_nsmul_le_sum
      intro ℓ hℓ
      rw [Finset.mem_filter, Finset.mem_range] at hℓ
      have := xUse_parity_const hk π hj ℓ (by omega)
      omega
    rw [smul_eq_mul] at htwo
    omega

/-- **Every tour costs at least `4k + 2`.** -/
theorem three_paths_opt_lower_thm (k : ℕ) (hk : 2 ≤ k) :
    (4 * k + 2 : ℝ) ≤ tspOpt (tpCost k) := by
  have hk1 : 1 ≤ k := by omega
  unfold tspOpt
  refine le_csInf ⟨tourCost (tpCost k) 1, 1, rfl⟩ ?_
  rintro t ⟨π, rfl⟩
  rw [tour_cost_eq hk1 π]
  have hbound : 4*k+2 ≤ ∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1), xUse k π j ℓ := by
    have h0 := path_total hk1 π (j := 0) (by omega)
    have h1 := path_total hk1 π (j := 1) (by omega)
    have h2 := path_total hk1 π (j := 2) (by omega)
    have hpar := xUse_hub_parity hk1 π
    have hexp : ∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1), xUse k π j ℓ
        = (∑ ℓ ∈ Finset.range (k+1), xUse k π 0 ℓ)
          + (∑ ℓ ∈ Finset.range (k+1), xUse k π 1 ℓ)
          + (∑ ℓ ∈ Finset.range (k+1), xUse k π 2 ℓ) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_zero]
      omega
    rw [hexp]
    have hp0 : xUse k π 0 0 % 2 = 0 ∨ xUse k π 0 0 % 2 = 1 := by omega
    have hp1 : xUse k π 1 0 % 2 = 0 ∨ xUse k π 1 0 % 2 = 1 := by omega
    have hp2 : xUse k π 2 0 % 2 = 0 ∨ xUse k π 2 0 % 2 = 1 := by omega
    rcases hp0 with hp0 | hp0 <;> rcases hp1 with hp1 | hp1 <;> rcases hp2 with hp2 | hp2
    · have := h0.2 hp0
      have := h1.2 hp1
      have := h2.2 hp2
      omega
    · omega
    · omega
    · have := h0.2 hp0
      have := h1.1 hp1
      have := h2.1 hp2
      omega
    · omega
    · have := h0.1 hp0
      have := h1.2 hp1
      have := h2.1 hp2
      omega
    · have := h0.1 hp0
      have := h1.1 hp1
      have := h2.2 hp2
      omega
    · omega
  have hcast : ((4*k+2 : ℕ) : ℝ) ≤ ((∑ j ∈ Finset.range 3, ∑ ℓ ∈ Finset.range (k+1),
      xUse k π j ℓ : ℕ) : ℝ) := by
    exact_mod_cast hbound
  calc (4 * k + 2 : ℝ) = ((4*k+2 : ℕ) : ℝ) := by push_cast; ring
    _ ≤ _ := hcast

end MetricTSP

open MetricTSP

theorem solution (k : ℕ) (hk : 2 ≤ k) :
    (4 * k + 2 : ℝ) ≤ tspOpt (tpCost k) :=
  MetricTSP.three_paths_opt_lower_thm k hk

