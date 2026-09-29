-- Prove2me | solution 1 for KServer.chunk_regroup
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T12:40:11.436513+00:00
-- url     : https://prove2.me/submissions/446ed43b-4451-43c3-a45d-e3d93e214db8

import Mathlib
import Definitions.Def_KServer_evader
import Definitions.Def_KServer_evader_bail
import Definitions.Def_KServer_chunk_system_b
import Definitions.Def_KServer_chunk_cond
import Definitions.Def_KServer_chunk_stopping
import Definitions.Def_KServer_bail_append
import Definitions.Def_KServer_chunk_saturate

set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1600000

open KServer

namespace Combine2

variable {X : Type*} [MetricSpace X] {s t : X} {cA cB T pe : ℝ} {mL : ℕ}

section Setup

variable (C : ChunkSystemB X s t cA cB T pe mL) (M : ℕ) (δ : ℝ)

/-- The chunk mass accumulated on `[a, h)`. -/
noncomputable def wmass (a h : ℕ) (ω : C.Ω) : ℝ :=
  ∑ j ∈ Finset.Ico a h, C.sizeN j ω

/-- The first time after `a` at which the accumulated mass reaches `2δ`
(with the input length as a sentinel). -/
noncomputable def massStop (a : ℕ) (ω : C.Ω) : ℕ :=
  sInf {h | (a < h ∧ 2 * δ ≤ wmass C a h ω) ∨ h = C.m}

/-- The window-end trigger after time `a` chasing the absolute level `x`:
the conditional future mass drops to `x`, or the accumulated mass since `a`
reaches `2δ`, with sentinel `C.m`. -/
noncomputable def trig (x : ℝ) (a : ℕ) (ω : C.Ω) : ℕ :=
  sInf {h | (a < h ∧ (C.condFuture h ω ≤ x
    ∨ 2 * δ ≤ wmass C a h ω)) ∨ h = C.m}

/-- The window boundaries: nested, strictly increasing, capped so that
exactly `M` nonempty windows partition `[0, C.m)`. -/
noncomputable def τ2 : ℕ → C.Ω → ℕ
  | 0 => fun _ => 0
  | (k + 1) => fun ω =>
      if M ≤ k + 1 then C.m
      else min (C.m - (M - (k + 1)))
        (max (τ2 k ω + 1)
          (trig C δ (C.expTotal - (k + 1) * δ) (τ2 k ω) ω))

/-- The **effective end** of window `k`: its boundary, but never beyond the
mass stop — the accounting of the window's size stops once mass `2δ` has
accumulated (this only matters for the final, forced window). -/
noncomputable def eend (k : ℕ) (ω : C.Ω) : ℕ :=
  min (τ2 C M δ (k + 1) ω) (max (τ2 C M δ k ω + 1) (massStop C δ (τ2 C M δ k ω) ω))

end Setup

section Bounds

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem τ2_zero (ω : C.Ω) : τ2 C M δ 0 ω = 0 := rfl

theorem τ2_last {k : ℕ} (hk : M ≤ k) (hM0 : 0 < M) (ω : C.Ω) :
    τ2 C M δ k ω = C.m := by
  rcases k with - | k
  · omega
  · unfold τ2
    rw [if_pos hk]

theorem τ2_le {k : ℕ} (hk : k ≤ M) (hMm : M ≤ C.m) (ω : C.Ω) :
    τ2 C M δ k ω ≤ C.m - (M - k) := by
  induction k with
  | zero =>
    rw [τ2_zero]
    omega
  | succ k ih =>
    unfold τ2
    by_cases hM : M ≤ k + 1
    · rw [if_pos hM]
      omega
    · rw [if_neg hM]
      omega

theorem τ2_le_m {k : ℕ} (hk : k ≤ M) (hMm : M ≤ C.m) (ω : C.Ω) :
    τ2 C M δ k ω ≤ C.m := by
  have h1 : τ2 C M δ k ω ≤ C.m - (M - k) := τ2_le hk hMm ω
  omega

theorem τ2_succ_def (C : ChunkSystemB X s t cA cB T pe mL) (M : ℕ) (δ : ℝ)
    (k : ℕ) (ω : C.Ω) :
    τ2 C M δ (k + 1) ω = if M ≤ k + 1 then C.m
      else min (C.m - (M - (k + 1)))
        (max (τ2 C M δ k ω + 1)
          (trig C δ (C.expTotal - (k + 1) * δ) (τ2 C M δ k ω) ω)) := rfl

theorem τ2_lt_succ {k : ℕ} (hk : k + 1 ≤ M) (hMm : M ≤ C.m) (ω : C.Ω) :
    τ2 C M δ k ω < τ2 C M δ (k + 1) ω := by
  have hkle : τ2 C M δ k ω ≤ C.m - (M - k) := τ2_le (by omega) hMm ω
  rw [τ2_succ_def]
  by_cases hM : M ≤ k + 1
  · rw [if_pos hM]
    omega
  · rw [if_neg hM]
    omega

theorem τ2_mono {k k' : ℕ} (hkk : k ≤ k') (hk : k' ≤ M) (hMm : M ≤ C.m)
    (ω : C.Ω) : τ2 C M δ k ω ≤ τ2 C M δ k' ω := by
  induction k', hkk using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
    exact le_trans (ih (by omega)) (le_of_lt (τ2_lt_succ hk hMm ω))

/-- The sentinel guarantees membership sets are nonempty. -/
theorem massStop_le_m (a : ℕ) (ω : C.Ω) : massStop C δ a ω ≤ C.m :=
  Nat.sInf_le (by simp)

theorem trig_le_m (x : ℝ) (a : ℕ) (ω : C.Ω) : trig C δ x a ω ≤ C.m :=
  Nat.sInf_le (by simp)

/-- The trigger fires no later than the mass stop. -/
theorem trig_le_massStop (x : ℝ) (a : ℕ) (ω : C.Ω) :
    trig C δ x a ω ≤ massStop C δ a ω := by
  have hmem := Nat.sInf_mem (⟨C.m, by simp⟩ :
    {h | (a < h ∧ 2 * δ ≤ wmass C a h ω) ∨ h = C.m}.Nonempty)
  simp only [Set.mem_setOf_eq] at hmem
  refine Nat.sInf_le ?_
  simp only [Set.mem_setOf_eq]
  rcases hmem with ⟨h1, h2⟩ | h1
  · exact Or.inl ⟨h1, Or.inr h2⟩
  · exact Or.inr h1

/-- Below the mass stop, the accumulated mass stays below `2δ`. -/
theorem wmass_lt_of_lt_massStop {a h : ℕ} {ω : C.Ω}
    (hh : h < massStop C δ a ω) (hm : h ≠ C.m) (ha : a < h) :
    wmass C a h ω < 2 * δ := by
  by_contra hcon
  push_neg at hcon
  have hmem : h ∈ {h | (a < h ∧ 2 * δ ≤ wmass C a h ω) ∨ h = C.m} := by
    simp only [Set.mem_setOf_eq]
    exact Or.inl ⟨ha, hcon⟩
  have hle : massStop C δ a ω ≤ h := Nat.sInf_le hmem
  omega

/-- Windows are nonempty also in effective form. -/
theorem lt_eend {k : ℕ} (hk : k + 1 ≤ M) (hMm : M ≤ C.m) (ω : C.Ω) :
    τ2 C M δ k ω < eend C M δ k ω := by
  unfold eend
  have h1 : τ2 C M δ k ω < τ2 C M δ (k + 1) ω := τ2_lt_succ hk hMm ω
  omega

theorem eend_le {k : ℕ} (ω : C.Ω) :
    eend C M δ k ω ≤ τ2 C M δ (k + 1) ω := min_le_left _ _

/-- The pointwise mass of one effective window is at most `2δ` plus one
chunk. -/
theorem wmass_eend_le {k : ℕ} (hk : k + 1 ≤ M) (hMm : M ≤ C.m)
    (hδ : 0 < δ) (hcB0 : 0 ≤ cB) (ω : C.Ω) :
    wmass C (τ2 C M δ k ω) (eend C M δ k ω) ω ≤ 2 * δ + cB := by
  set a := τ2 C M δ k ω with ha
  set e := eend C M δ k ω with he
  have hae : a < e := lt_eend hk hMm ω
  have hem : e ≤ C.m := by
    have h1 : τ2 C M δ (k+1) ω ≤ C.m := τ2_le_m (by omega) hMm ω
    have h2 := eend_le (C := C) (M := M) (δ := δ) (k := k) ω
    omega
  have hems : e ≤ max (a + 1) (massStop C δ a ω) := by
    rw [he]
    unfold eend
    exact min_le_right _ _
  rcases Nat.eq_or_lt_of_le hae with heq | hlt
  · -- single-chunk window
    unfold wmass
    rw [← heq, Finset.sum_Ico_succ_top (le_refl a), Finset.Ico_self,
      Finset.sum_empty, zero_add]
    have := C.sizeN_le (show a < C.m by omega) ω
    linarith
  · have hstep : wmass C a (e - 1) ω < 2 * δ := by
      rcases Nat.lt_or_ge a (e - 1) with h1 | h1
      · have hlt2 : e - 1 < massStop C δ a ω := by omega
        exact wmass_lt_of_lt_massStop hlt2 (by omega) h1
      · have hempty : Finset.Ico a (e - 1) = ∅ := Finset.Ico_eq_empty (by omega)
        unfold wmass
        rw [hempty, Finset.sum_empty]
        linarith
    have hsplit : wmass C a e ω = wmass C a (e - 1) ω + C.sizeN (e - 1) ω := by
      unfold wmass
      conv_lhs => rw [show e = (e - 1) + 1 by omega]
      rw [Finset.sum_Ico_succ_top (by omega)]
    have hlast : C.sizeN (e - 1) ω ≤ cB := C.sizeN_le (by omega) ω
    linarith

end Bounds

section Congr

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem chunk_agree2 {b : ℕ} {ω ω' : C.Ω} (hh : C.hist b ω = C.hist b ω')
    {j : Fin C.m} (hj : (j : ℕ) < b) : C.chunk ω j = C.chunk ω' j :=
  C.hadapt j ω ω' (C.href ((j : ℕ) + 1) b (by omega) ω ω' hh)

theorem take_ofFn_agree {b : ℕ} {ω ω' : C.Ω} (hh : C.hist b ω = C.hist b ω') :
    (List.ofFn (C.chunk ω)).take b = (List.ofFn (C.chunk ω')).take b := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_ofFn]
    have hkb : k < b := by
      simp only [List.length_take, List.length_ofFn] at h1
      omega
    exact chunk_agree2 hh hkb

theorem wmass_congr {b : ℕ} {ω ω' : C.Ω} (hh : C.hist b ω' = C.hist b ω)
    {a h : ℕ} (hb : h ≤ b) : wmass C a h ω' = wmass C a h ω := by
  unfold wmass
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_Ico] at hj
  exact C.sizeN_congr (C.href j b (by omega) ω' ω hh)

theorem massStop_mem_iff {b : ℕ} {ω ω' : C.Ω}
    (hh : C.hist b ω' = C.hist b ω) {a h : ℕ} (hb : h ≤ b) :
    ((a < h ∧ 2 * δ ≤ wmass C a h ω) ∨ h = C.m)
      ↔ ((a < h ∧ 2 * δ ≤ wmass C a h ω') ∨ h = C.m) := by
  rw [wmass_congr hh hb]

theorem massStop_congr {b : ℕ} {ω ω' : C.Ω}
    (hh : C.hist b ω' = C.hist b ω) {a : ℕ}
    (hle : massStop C δ a ω ≤ b) : massStop C δ a ω' = massStop C δ a ω := by
  have h1 : massStop C δ a ω' ≤ massStop C δ a ω := by
    refine Nat.sInf_le ?_
    have hmem := Nat.sInf_mem (⟨C.m, by simp⟩ :
      {h | (a < h ∧ 2 * δ ≤ wmass C a h ω) ∨ h = C.m}.Nonempty)
    simp only [Set.mem_setOf_eq] at hmem ⊢
    exact (massStop_mem_iff hh hle).mp hmem
  rcases Nat.lt_or_ge (massStop C δ a ω') (massStop C δ a ω) with hlt | hge
  · exfalso
    have hmem' := Nat.sInf_mem (⟨C.m, by simp⟩ :
      {h | (a < h ∧ 2 * δ ≤ wmass C a h ω') ∨ h = C.m}.Nonempty)
    simp only [Set.mem_setOf_eq] at hmem'
    have hmem : massStop C δ a ω' ∈
        {h | (a < h ∧ 2 * δ ≤ wmass C a h ω) ∨ h = C.m} := by
      simp only [Set.mem_setOf_eq]
      exact (massStop_mem_iff hh (by omega)).mpr hmem'
    have h2 : massStop C δ a ω ≤ massStop C δ a ω' := Nat.sInf_le hmem
    omega
  · omega

theorem massStop_gt {b : ℕ} {ω ω' : C.Ω}
    (hh : C.hist b ω' = C.hist b ω) {a : ℕ}
    (hgt : b < massStop C δ a ω) : b < massStop C δ a ω' := by
  by_contra hcon
  push_neg at hcon
  have h1 : massStop C δ a ω = massStop C δ a ω' :=
    massStop_congr (by rw [hh]) hcon
  omega

theorem trig_mem_iff {b : ℕ} {ω ω' : C.Ω}
    (hh : C.hist b ω' = C.hist b ω) {x : ℝ} {a h : ℕ} (hb : h ≤ b) :
    ((a < h ∧ (C.condFuture h ω ≤ x ∨ 2 * δ ≤ wmass C a h ω)) ∨ h = C.m)
      ↔ ((a < h ∧ (C.condFuture h ω' ≤ x ∨ 2 * δ ≤ wmass C a h ω')) ∨ h = C.m) := by
  rw [wmass_congr hh hb, C.condFuture_congr (C.href h b hb ω' ω hh)]

theorem trig_congr {b : ℕ} {ω ω' : C.Ω}
    (hh : C.hist b ω' = C.hist b ω) {x : ℝ} {a : ℕ}
    (hle : trig C δ x a ω ≤ b) : trig C δ x a ω' = trig C δ x a ω := by
  have h1 : trig C δ x a ω' ≤ trig C δ x a ω := by
    refine Nat.sInf_le ?_
    have hmem := Nat.sInf_mem (⟨C.m, by simp⟩ :
      {h | (a < h ∧ (C.condFuture h ω ≤ x ∨ 2 * δ ≤ wmass C a h ω))
        ∨ h = C.m}.Nonempty)
    simp only [Set.mem_setOf_eq] at hmem ⊢
    exact (trig_mem_iff hh hle).mp hmem
  rcases Nat.lt_or_ge (trig C δ x a ω') (trig C δ x a ω) with hlt | hge
  · exfalso
    have hmem' := Nat.sInf_mem (⟨C.m, by simp⟩ :
      {h | (a < h ∧ (C.condFuture h ω' ≤ x ∨ 2 * δ ≤ wmass C a h ω'))
        ∨ h = C.m}.Nonempty)
    simp only [Set.mem_setOf_eq] at hmem'
    have hmem : trig C δ x a ω' ∈
        {h | (a < h ∧ (C.condFuture h ω ≤ x ∨ 2 * δ ≤ wmass C a h ω))
          ∨ h = C.m} := by
      simp only [Set.mem_setOf_eq]
      exact (trig_mem_iff hh (by omega)).mpr hmem'
    have h2 : trig C δ x a ω ≤ trig C δ x a ω' := Nat.sInf_le hmem
    omega
  · omega

theorem trig_gt {b : ℕ} {ω ω' : C.Ω}
    (hh : C.hist b ω' = C.hist b ω) {x : ℝ} {a : ℕ}
    (hgt : b < trig C δ x a ω) : b < trig C δ x a ω' := by
  by_contra hcon
  push_neg at hcon
  have h1 : trig C δ x a ω = trig C δ x a ω' := trig_congr (by rw [hh]) hcon
  omega

/-- The boundaries are stopping times: determined by the history at any
level they have not passed. -/
theorem τ2_congr (hMm : M ≤ C.m) :
    ∀ (k : ℕ), k ≤ M → ∀ {b : ℕ} {ω ω' : C.Ω},
    C.hist b ω' = C.hist b ω → τ2 C M δ k ω ≤ b →
    τ2 C M δ k ω' = τ2 C M δ k ω := by
  intro k
  induction k with
  | zero =>
    intro _ b ω ω' hh _
    rw [τ2_zero, τ2_zero]
  | succ k ih =>
    intro hk b ω ω' hh hle
    by_cases hM : M ≤ k + 1
    · rw [τ2_succ_def, τ2_succ_def, if_pos hM, if_pos hM]
    · have hklt : τ2 C M δ k ω < τ2 C M δ (k + 1) ω := τ2_lt_succ (by omega) hMm ω
      have hkb : τ2 C M δ k ω ≤ b := by omega
      have hτk : τ2 C M δ k ω' = τ2 C M δ k ω := ih (by omega) hh hkb
      rw [τ2_succ_def, τ2_succ_def, if_neg hM, if_neg hM, hτk]
      set a := τ2 C M δ k ω
      set x := C.expTotal - (k + 1) * δ
      rcases Nat.lt_or_ge b (trig C δ x a ω) with htr | htr
      · -- the trigger lies beyond `b` for both outcomes
        have htr' : b < trig C δ x a ω' := trig_gt hh htr
        -- the value is then the cap on both sides
        have hval : τ2 C M δ (k + 1) ω
            = min (C.m - (M - (k + 1))) (max (a + 1) (trig C δ x a ω)) := by
          rw [τ2_succ_def, if_neg hM]
        rw [hval] at hle hklt
        omega
      · have htr' : trig C δ x a ω' = trig C δ x a ω := trig_congr hh htr
        rw [htr']

theorem eend_congr (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M) {b : ℕ}
    {ω ω' : C.Ω} (hh : C.hist b ω' = C.hist b ω)
    (hle : eend C M δ k ω ≤ b) : eend C M δ k ω' = eend C M δ k ω := by
  have hklt : τ2 C M δ k ω < eend C M δ k ω := lt_eend hk hMm ω
  have hkb : τ2 C M δ k ω ≤ b := by omega
  have hτk : τ2 C M δ k ω' = τ2 C M δ k ω := τ2_congr hMm k (by omega) hh hkb
  have hdef : eend C M δ k ω = min (τ2 C M δ (k + 1) ω)
      (max (τ2 C M δ k ω + 1) (massStop C δ (τ2 C M δ k ω) ω)) := rfl
  have hdef' : eend C M δ k ω' = min (τ2 C M δ (k + 1) ω')
      (max (τ2 C M δ k ω + 1) (massStop C δ (τ2 C M δ k ω) ω')) := by
    unfold eend
    rw [hτk]
  rcases Nat.lt_or_ge b (τ2 C M δ (k + 1) ω) with h1 | h1
  · have h1' : b < τ2 C M δ (k + 1) ω' := by
      by_contra hcon
      push_neg at hcon
      have h2 := τ2_congr hMm (k + 1) hk
        (show C.hist b ω = C.hist b ω' from hh.symm) hcon
      omega
    have hmsle : massStop C δ (τ2 C M δ k ω) ω ≤ b := by omega
    have hms := massStop_congr hh hmsle
    omega
  · have h1' : τ2 C M δ (k + 1) ω' = τ2 C M δ (k + 1) ω :=
      τ2_congr hMm (k + 1) hk hh h1
    rcases Nat.lt_or_ge b (massStop C δ (τ2 C M δ k ω) ω) with h2 | h2
    · have h2' : b < massStop C δ (τ2 C M δ k ω) ω' := massStop_gt hh h2
      omega
    · have h2' := massStop_congr hh h2
      omega

end Congr

section Output

variable (C : ChunkSystemB X s t cA cB T pe mL) (M : ℕ) (δ : ℝ)

/-- Output history: boundary time paired with the fine history there. -/
noncomputable def whist2 (n : ℕ) (ω : C.Ω) : ℕ :=
  Nat.pair (τ2 C M δ n ω) (C.hist (τ2 C M δ n ω) ω)

/-- Output chunks: the input chunks of one window, concatenated. -/
noncomputable def wchunk2 (ω : C.Ω) (k : ℕ) : List (Set X) :=
  (((List.ofFn (C.chunk ω)).take (τ2 C M δ (k + 1) ω)).drop (τ2 C M δ k ω)).flatten

/-- Output sizes: conditional effective window masses. -/
noncomputable def wsize2 (k : ℕ) (ω : C.Ω) : ℝ :=
  C.condExp (fun ω' => wmass C (τ2 C M δ k ω') (eend C M δ k ω') ω')
    (τ2 C M δ k ω) ω

end Output

section OutputLemmas

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem whist2_pair {n : ℕ} {ω ω' : C.Ω} :
    whist2 C M δ n ω = whist2 C M δ n ω'
      ↔ τ2 C M δ n ω = τ2 C M δ n ω'
        ∧ C.hist (τ2 C M δ n ω) ω = C.hist (τ2 C M δ n ω) ω' := by
  unfold whist2
  rw [Nat.pair_eq_pair]
  constructor
  · rintro ⟨he, hf⟩
    rw [← he] at hf
    exact ⟨he, hf⟩
  · rintro ⟨he, hf⟩
    rw [← he]
    exact ⟨rfl, hf⟩

theorem whist2_ref (hMm : M ≤ C.m) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ M)
    {ω ω' : C.Ω} (hh : whist2 C M δ j ω = whist2 C M δ j ω') :
    whist2 C M δ i ω = whist2 C M δ i ω' := by
  obtain ⟨he, hf⟩ := whist2_pair.mp hh
  have hτi : τ2 C M δ i ω ≤ τ2 C M δ j ω := τ2_mono hij hj hMm ω
  have hτeq : τ2 C M δ i ω' = τ2 C M δ i ω :=
    τ2_congr hMm i (by omega) hf.symm hτi
  rw [whist2_pair]
  refine ⟨hτeq.symm, ?_⟩
  exact C.href (τ2 C M δ i ω) (τ2 C M δ j ω) hτi ω ω' hf

theorem wchunk2_congr (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M) {ω ω' : C.Ω}
    (hh : whist2 C M δ (k + 1) ω = whist2 C M δ (k + 1) ω') :
    wchunk2 C M δ ω k = wchunk2 C M δ ω' k := by
  obtain ⟨he, hf⟩ := whist2_pair.mp hh
  have hτk : τ2 C M δ k ω ≤ τ2 C M δ (k + 1) ω :=
    le_of_lt (τ2_lt_succ hk hMm ω)
  have hτeq : τ2 C M δ k ω' = τ2 C M δ k ω :=
    τ2_congr hMm k (by omega) hf.symm hτk
  unfold wchunk2
  rw [← he, hτeq, take_ofFn_agree hf]

theorem wsize2_congr (hMm : M ≤ C.m) {k : ℕ} {ω ω' : C.Ω}
    (hh : whist2 C M δ k ω = whist2 C M δ k ω') :
    wsize2 C M δ k ω = wsize2 C M δ k ω' := by
  obtain ⟨he, hf⟩ := whist2_pair.mp hh
  unfold wsize2
  rw [← he]
  exact (C.condExp_congr _ hf.symm).symm

/-- Windows partition the input sequence. -/
theorem wchunk2_prefix (hMm : M ≤ C.m) (ω : C.Ω) (i : ℕ) (hi : i ≤ M) :
    ((List.ofFn (fun k : Fin M => wchunk2 C M δ ω (k : ℕ))).take i).flatten
      = ((List.ofFn (C.chunk ω)).take (τ2 C M δ i ω)).flatten := by
  induction i with
  | zero =>
    rw [τ2_zero]
    simp
  | succ i ih =>
    have hiM : i < M := by omega
    have htake : (List.ofFn (fun k : Fin M => wchunk2 C M δ ω (k : ℕ))).take (i + 1)
        = (List.ofFn (fun k : Fin M => wchunk2 C M δ ω (k : ℕ))).take i
          ++ [wchunk2 C M δ ω i] := by
      rw [List.take_succ]
      congr 1
      rw [List.getElem?_eq_getElem (by simp [hiM])]
      simp only [List.getElem_ofFn]
      rfl
    rw [htake, List.flatten_append, ih (by omega)]
    unfold wchunk2
    rw [List.flatten_cons, List.flatten_nil, List.append_nil]
    have hτi : τ2 C M δ i ω ≤ τ2 C M δ (i + 1) ω :=
      le_of_lt (τ2_lt_succ (by omega) hMm ω)
    rw [← List.flatten_append]
    congr 1
    have hsplit := List.take_append_drop (τ2 C M δ i ω)
      ((List.ofFn (C.chunk ω)).take (τ2 C M δ (i + 1) ω))
    rw [List.take_take, min_eq_left hτi] at hsplit
    exact hsplit

theorem wchunk2_flatten (hMm : M ≤ C.m) (hM0 : 0 < M) (ω : C.Ω) :
    (List.ofFn (fun k : Fin M => wchunk2 C M δ ω (k : ℕ))).flatten
      = (List.ofFn (C.chunk ω)).flatten := by
  have h1 := wchunk2_prefix (C := C) (δ := δ) hMm ω M (le_refl M)
  rw [List.take_of_length_le (by simp)] at h1
  rw [τ2_last (le_refl M) hM0 ω, List.take_of_length_le (by simp)] at h1
  exact h1

theorem wchunk2_ne (ω : C.Ω) (k : ℕ) : ∀ S ∈ wchunk2 C M δ ω k, S.Nonempty := by
  intro S hS
  unfold wchunk2 at hS
  rw [List.mem_flatten] at hS
  obtain ⟨l, hl, hSl⟩ := hS
  have hl2 : l ∈ List.ofFn (C.chunk ω) :=
    List.mem_of_mem_take (List.mem_of_mem_drop hl)
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hl2
  refine C.hne ω j S ?_
  rw [hj]
  exact hSl

/-- Pointwise size bounds: nonnegative and at most `2δ + cB`. -/
theorem wsize2_nonneg (hcA0 : 0 ≤ cA) (k : ℕ) (ω : C.Ω) :
    0 ≤ wsize2 C M δ k ω :=
  C.le_condExp fun ω' _ => Finset.sum_nonneg fun j _ => C.sizeN_nonneg hcA0 j ω'

theorem wsize2_le (hMm : M ≤ C.m) (hδ : 0 < δ) (hcB0 : 0 ≤ cB)
    {k : ℕ} (hk : k + 1 ≤ M) (ω : C.Ω) :
    wsize2 C M δ k ω ≤ 2 * δ + cB :=
  C.condExp_le fun ω' _ => wmass_eend_le hk hMm hδ hcB0 ω'

end OutputLemmas

section Charge

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem eend_gt (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M) {b : ℕ}
    {ω ω' : C.Ω} (hh : C.hist b ω' = C.hist b ω)
    (hgt : b < eend C M δ k ω) : b < eend C M δ k ω' := by
  by_contra hcon
  push_neg at hcon
  have h1 := eend_congr hMm hk (show C.hist b ω = C.hist b ω' from hh.symm) hcon
  omega

/-- The bail-aware cost of the rest of window `k` from input position `j`. -/
noncomputable def wcost2 (C : ChunkSystemB X s t cA cB T pe mL) (M : ℕ) (δ : ℝ)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    (p' : ℝ) (k j : ℕ) (ω : C.Ω) : ℝ :=
  E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
    ((((List.ofFn (C.chunk ω)).take (τ2 C M δ (k + 1) ω)).drop j).flatten) p'

theorem take_flatten_succ2 (ω : C.Ω) {j : ℕ} (hj : j < C.m) :
    ((List.ofFn (C.chunk ω)).take (j + 1)).flatten
      = ((List.ofFn (C.chunk ω)).take j).flatten ++ C.chunk ω ⟨j, hj⟩ := by
  have h1 : (List.ofFn (C.chunk ω)).take (j + 1)
      = (List.ofFn (C.chunk ω)).take j ++ [C.chunk ω ⟨j, hj⟩] := by
    rw [List.take_succ]
    congr 1
    rw [List.getElem?_eq_getElem (by simp [hj])]
    simp only [List.getElem_ofFn]
    rfl
  rw [h1, List.flatten_append, List.flatten_cons, List.flatten_nil,
    List.append_nil]

theorem window_cons2 (hMm : M ≤ C.m) (ω : C.Ω) {k j : ℕ} (hk : k + 1 ≤ M)
    (hj : j < τ2 C M δ (k + 1) ω) :
    (((List.ofFn (C.chunk ω)).take (τ2 C M δ (k + 1) ω)).drop j)
      = C.chunk ω ⟨j, lt_of_lt_of_le hj (τ2_le_m hk hMm ω)⟩
        :: (((List.ofFn (C.chunk ω)).take (τ2 C M δ (k + 1) ω)).drop (j + 1)) := by
  have hjm : j < C.m := lt_of_lt_of_le hj (τ2_le_m hk hMm ω)
  have hlen : j < ((List.ofFn (C.chunk ω)).take (τ2 C M δ (k + 1) ω)).length := by
    simp only [List.length_take, List.length_ofFn]
    omega
  rw [List.drop_eq_getElem_cons hlen]
  congr 1
  rw [List.getElem_take, List.getElem_ofFn]

theorem wcost2_step_no_bail (hMm : M ≤ C.m)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (p' : ℝ)
    {k j : ℕ} (hk : k + 1 ≤ M) (ω : C.Ω) (hj : j < τ2 C M δ (k + 1) ω)
    (hbail : bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
      (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ2_le_m hk hMm ω)⟩) = none) :
    wcost2 C M δ E bail p' k j ω
      = E.costOn (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ2_le_m hk hMm ω)⟩)
        + wcost2 C M δ E bail p' k (j + 1) ω := by
  have hjm : j < C.m := lt_of_lt_of_le hj (τ2_le_m hk hMm ω)
  unfold wcost2
  rw [window_cons2 hMm ω hk hj, List.flatten_cons,
    E.bailCost_append_of_no_bail bail _ _ _ _ hbail,
    ← take_flatten_succ2 ω hjm]

theorem wcost2_step_bail (hMm : M ≤ C.m)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool) (p' : ℝ)
    {k j q : ℕ} (hk : k + 1 ≤ M) (ω : C.Ω) (hj : j < τ2 C M δ (k + 1) ω)
    (hbail : bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
      (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ2_le_m hk hMm ω)⟩) = some q) :
    wcost2 C M δ E bail p' k j ω
      = E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, lt_of_lt_of_le hj (τ2_le_m hk hMm ω)⟩) pe
        + (p' - pe) := by
  have hjm : j < C.m := lt_of_lt_of_le hj (τ2_le_m hk hMm ω)
  unfold wcost2
  rw [window_cons2 hMm ω hk hj, List.flatten_cons,
    E.bailCost_append_of_bail bail _ _ _ _ hbail,
    E.bailCost_price_of_bail bail _ _ pe p' hbail]

theorem wcost2_nonneg (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {p' : ℝ} (hp' : 0 ≤ p') (k j : ℕ) (ω : C.Ω) :
    0 ≤ wcost2 C M δ E bail p' k j ω :=
  E.bailCost_nonneg bail _ _ hp'

end Charge

section ChargeClaim

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

/-- The bail rule is quiet on all complete input chunks in `[a, j)`. -/
def quiet2 (bail : List (Set X) → Bool) (a j : ℕ) (ω : C.Ω) : Prop :=
  ∀ k, a ≤ k → k < j → ∀ hk : k < C.m,
    bailTime bail (((List.ofFn (C.chunk ω)).take k).flatten)
      (C.chunk ω ⟨k, hk⟩) = none

open Classical in
/-- The charging induction for v2: truncated remaining window mass is
dominated by the bail-aware cost, with escapes financed pointwise. -/
theorem charge2 (hMm : M ≤ C.m) (hM0 : 0 < M)
    (hcA0 : 0 ≤ cA) (hδ : 0 < δ) (hcB0 : 0 ≤ cB)
    {p' : ℝ} (hp : pe + (2 * δ + cB) ≤ p') (hpe : 0 ≤ pe)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {k : ℕ} (hk : k + 1 ≤ M) (ω₀ : C.Ω) :
    ∀ d j, τ2 C M δ k ω₀ ≤ j → C.m ≤ j + d →
    ∑ ω ∈ (C.atom (τ2 C M δ k ω₀) ω₀).filter
        (fun ω => j < eend C M δ k ω ∧ quiet2 bail (τ2 C M δ k ω₀) j ω),
      C.P ω * (∑ i ∈ Finset.Ico j (eend C M δ k ω), C.sizeN i ω)
    ≤ ∑ ω ∈ (C.atom (τ2 C M δ k ω₀) ω₀).filter
        (fun ω => j < eend C M δ k ω ∧ quiet2 bail (τ2 C M δ k ω₀) j ω),
      C.P ω * wcost2 C M δ E bail p' k j ω := by
  have hp0 : 0 ≤ p' := by linarith
  have hempty : ∀ j, C.m ≤ j →
      (C.atom (τ2 C M δ k ω₀) ω₀).filter
        (fun ω => j < eend C M δ k ω ∧ quiet2 bail (τ2 C M δ k ω₀) j ω) = ∅ := by
    intro j hj
    rw [Finset.filter_eq_empty_iff]
    rintro ω - ⟨h1, -⟩
    have h2 : eend C M δ k ω ≤ τ2 C M δ (k + 1) ω := eend_le ω
    have h3 : τ2 C M δ (k + 1) ω ≤ C.m := τ2_le_m hk hMm ω
    omega
  intro d
  induction d with
  | zero =>
    intro j haj hjd
    rw [hempty j (by omega)]
    simp
  | succ d ih =>
    intro j haj hjd
    by_cases hjm : C.m ≤ j
    · rw [hempty j hjm]
      simp
    · push_neg at hjm
      set a := τ2 C M δ k ω₀ with ha_def
      set NBW := (C.atom a ω₀).filter
        (fun ω => j < eend C M δ k ω ∧ quiet2 bail a j ω) with hNBW_def
      have hmemA : ∀ ω ∈ NBW, C.hist a ω = C.hist a ω₀ := by
        intro ω hm
        rw [hNBW_def, Finset.mem_filter] at hm
        exact C.mem_atom.mp hm.1
      have hb_NBW : ∀ ω ∈ NBW, j < eend C M δ k ω := by
        intro ω hm
        rw [hNBW_def, Finset.mem_filter] at hm
        exact hm.2.1
      have hb_win : ∀ ω ∈ NBW, j < τ2 C M δ (k + 1) ω := by
        intro ω hm
        have h1 := hb_NBW ω hm
        have h2 : eend C M δ k ω ≤ τ2 C M δ (k + 1) ω := eend_le ω
        omega
      have hpeel : ∀ ω ∈ NBW,
          ∑ i ∈ Finset.Ico j (eend C M δ k ω), C.sizeN i ω
            = C.sizeN j ω + ∑ i ∈ Finset.Ico (j + 1) (eend C M δ k ω), C.sizeN i ω := by
        intro ω hm
        exact Finset.sum_eq_sum_Ico_succ_bot (hb_NBW ω hm) _
      -- saturation at level j
      have hsat_NBW : ∀ ω ∈ NBW, ∀ ω', C.hist j ω' = C.hist j ω → ω' ∈ NBW := by
        intro ω hm ω' hh
        rw [hNBW_def, Finset.mem_filter] at hm ⊢
        have hA := hm.1
        have hb := hm.2.1
        have hq := hm.2.2
        refine ⟨?_, ?_, ?_⟩
        · rw [C.mem_atom] at hA ⊢
          exact (C.href a j haj ω' ω hh).trans hA
        · exact eend_gt hMm hk hh hb
        · intro i hai hij hi
          have hhk : C.hist i ω' = C.hist i ω := C.href i j (by omega) ω' ω hh
          have hhk1 : C.hist (i + 1) ω' = C.hist (i + 1) ω :=
            C.href (i + 1) j (by omega) ω' ω hh
          rw [take_ofFn_agree hhk, chunk_agree2 hhk1 (Nat.lt_succ_self i)]
          exact hq i hai hij hi
      -- the input premise at position j
      have hprem : ∑ ω ∈ NBW, C.P ω * C.sizeN j ω
          ≤ ∑ ω ∈ NBW, C.P ω *
              E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe := by
        refine ChunkSystemB.sum_saturated_le C j NBW hsat_NBW _ _ fun ω₁ _ => ?_
        have hpre : C.size ω₁ ⟨j, hjm⟩ * C.mass (C.atom j ω₁)
            ≤ ∑ ω' ∈ C.atom j ω₁, C.P ω' *
                E.bailCost bail (((List.ofFn (C.chunk ω')).take j).flatten)
                  (C.chunk ω' ⟨j, hjm⟩) pe := C.hcost ⟨j, hjm⟩ ω₁ E bail
        refine le_trans (le_of_eq ?_) hpre
        unfold ChunkSystemB.mass
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω' hm' => ?_
        unfold ChunkSystemB.sizeN
        rw [dif_pos hjm, C.hsmeas ⟨j, hjm⟩ ω' ω₁ (C.mem_atom.mp hm')]
        ring
      -- split by bail behaviour on chunk j and window end
      set cond1 : C.Ω → Prop := fun ω =>
        bailTime bail (((List.ofFn (C.chunk ω)).take j).flatten)
          (C.chunk ω ⟨j, hjm⟩) = none with hcond1_def
      set S1 := NBW.filter (fun ω => cond1 ω ∧ j + 1 < eend C M δ k ω) with hS1_def
      set S2 := NBW.filter (fun ω => cond1 ω ∧ ¬ j + 1 < eend C M δ k ω) with hS2_def
      set S3 := NBW.filter (fun ω => ¬ cond1 ω) with hS3_def
      have hS1_eq : S1 = (C.atom a ω₀).filter
          (fun ω => j + 1 < eend C M δ k ω ∧ quiet2 bail a (j + 1) ω) := by
        rw [hS1_def, hNBW_def, Finset.filter_filter]
        ext ω
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨hA, ⟨hb, hq⟩, hc1, hb1⟩
          refine ⟨hA, hb1, ?_⟩
          intro i hai hij hi
          rcases Nat.lt_or_ge i j with hij' | hij'
          · exact hq i hai hij' hi
          · have hieq : i = j := by omega
            subst hieq
            exact hc1
        · rintro ⟨hA, hb1, hq⟩
          have hc1 : cond1 ω := hq j haj (by omega) hjm
          exact ⟨hA, ⟨by omega, fun i hai hij hi => hq i hai (by omega) hi⟩, hc1, hb1⟩
      have hsplit0 : ∀ f : C.Ω → ℝ, ∑ ω ∈ NBW, f ω
          = (∑ ω ∈ S1, f ω + ∑ ω ∈ S2, f ω) + ∑ ω ∈ S3, f ω := by
        intro f
        have e1 : NBW.filter cond1 = S1 ∪ S2 := by
          rw [hS1_def, hS2_def]
          ext ω
          simp only [Finset.mem_filter, Finset.mem_union]
          tauto
        have hdisj : Disjoint S1 S2 := by
          rw [hS1_def, hS2_def, Finset.disjoint_filter]
          tauto
        rw [← Finset.sum_filter_add_sum_filter_not NBW cond1 f, e1,
          Finset.sum_union hdisj, hS3_def]
      have hS2_b : ∀ ω ∈ S2, eend C M δ k ω = j + 1 := by
        intro ω hm
        rw [hS2_def, Finset.mem_filter] at hm
        have h2 := hb_NBW ω hm.1
        have h1 := hm.2.2
        omega
      -- pointwise tail bound for the escape financing
      have htail_le : ∀ ω ∈ NBW,
          ∑ i ∈ Finset.Ico (j + 1) (eend C M δ k ω), C.sizeN i ω ≤ p' - pe := by
        intro ω hm
        have hsub : ∑ i ∈ Finset.Ico (j + 1) (eend C M δ k ω), C.sizeN i ω
            ≤ wmass C a (eend C M δ k ω) ω := by
          unfold wmass
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_
            (fun i _ _ => C.sizeN_nonneg hcA0 i ω)
          refine Finset.Ico_subset_Ico (by omega) (le_refl _)
        have haω : τ2 C M δ k ω = a :=
          τ2_congr hMm k (by omega) (hmemA ω hm) (le_refl a)
        have hcap : wmass C a (eend C M δ k ω) ω ≤ 2 * δ + cB := by
          rw [← haω]
          exact wmass_eend_le hk hMm hδ hcB0 ω
        linarith
      -- cost decomposition
      have hcost_S12 : ∀ ω ∈ NBW, cond1 ω →
          C.P ω * wcost2 C M δ E bail p' k j ω
            = C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe
              + C.P ω * wcost2 C M δ E bail p' k (j + 1) ω := by
        intro ω hm hc
        have hb := hb_win ω hm
        simp only [hcond1_def] at hc
        rw [wcost2_step_no_bail hMm E bail p' hk ω hb hc,
          E.bailCost_of_no_bail bail _ _ pe hc]
        ring
      have hcost_S3 : ∀ ω ∈ S3,
          C.P ω * wcost2 C M δ E bail p' k j ω
            = C.P ω * E.bailCost bail (((List.ofFn (C.chunk ω)).take j).flatten)
                (C.chunk ω ⟨j, hjm⟩) pe
              + C.P ω * (p' - pe) := by
        intro ω hm
        rw [hS3_def, Finset.mem_filter] at hm
        have hb := hb_win ω hm.1
        have hc := hm.2
        simp only [hcond1_def] at hc
        obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
        rw [wcost2_step_bail hMm E bail p' hk ω hb hq]
        ring
      have hS1_mem : ∀ ω ∈ S1, ω ∈ NBW ∧ cond1 ω := by
        intro ω hm
        rw [hS1_def, Finset.mem_filter] at hm
        exact ⟨hm.1, hm.2.1⟩
      have hS2_mem : ∀ ω ∈ S2, ω ∈ NBW ∧ cond1 ω := by
        intro ω hm
        rw [hS2_def, Finset.mem_filter] at hm
        exact ⟨hm.1, hm.2.1⟩
      have hS_sub : ∀ ω ∈ S3, ω ∈ NBW := by
        intro ω hm
        rw [hS3_def, Finset.mem_filter] at hm
        exact hm.1
      -- assemble
      have hLHS : ∑ ω ∈ NBW, C.P ω * (∑ i ∈ Finset.Ico j (eend C M δ k ω), C.sizeN i ω)
          = ∑ ω ∈ NBW, C.P ω * C.sizeN j ω
            + ((∑ ω ∈ S1, C.P ω * (∑ i ∈ Finset.Ico (j + 1) (eend C M δ k ω), C.sizeN i ω)
              + ∑ ω ∈ S2, C.P ω * (∑ i ∈ Finset.Ico (j + 1) (eend C M δ k ω), C.sizeN i ω))
              + ∑ ω ∈ S3, C.P ω * (∑ i ∈ Finset.Ico (j + 1) (eend C M δ k ω), C.sizeN i ω)) := by
        rw [Finset.sum_congr rfl fun ω hm => by rw [hpeel ω hm, mul_add],
          Finset.sum_add_distrib,
          hsplit0 (fun ω => C.P ω * (∑ i ∈ Finset.Ico (j + 1) (eend C M δ k ω), C.sizeN i ω))]
      have hRHS : ∑ ω ∈ NBW, C.P ω * wcost2 C M δ E bail p' k j ω
          = ∑ ω ∈ NBW, C.P ω * E.bailCost bail
              (((List.ofFn (C.chunk ω)).take j).flatten) (C.chunk ω ⟨j, hjm⟩) pe
            + ((∑ ω ∈ S1, C.P ω * wcost2 C M δ E bail p' k (j + 1) ω
              + ∑ ω ∈ S2, C.P ω * wcost2 C M δ E bail p' k (j + 1) ω)
              + ∑ ω ∈ S3, C.P ω * (p' - pe)) := by
        rw [hsplit0 (fun ω => C.P ω * wcost2 C M δ E bail p' k j ω),
          hsplit0 (fun ω => C.P ω * E.bailCost bail
            (((List.ofFn (C.chunk ω)).take j).flatten) (C.chunk ω ⟨j, hjm⟩) pe)]
        rw [Finset.sum_congr rfl fun ω hm =>
            hcost_S12 ω (hS1_mem ω hm).1 (hS1_mem ω hm).2,
          Finset.sum_congr rfl fun ω hm =>
            hcost_S12 ω (hS2_mem ω hm).1 (hS2_mem ω hm).2,
          Finset.sum_congr rfl (hcost_S3),
          Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
        ring
      rw [hLHS, hRHS]
      have hIH : ∑ ω ∈ S1, C.P ω *
            (∑ i ∈ Finset.Ico (j + 1) (eend C M δ k ω), C.sizeN i ω)
          ≤ ∑ ω ∈ S1, C.P ω * wcost2 C M δ E bail p' k (j + 1) ω := by
        rw [hS1_eq]
        exact ih (j + 1) (by omega) (by omega)
      have hS2_zero : ∑ ω ∈ S2, C.P ω *
            (∑ i ∈ Finset.Ico (j + 1) (eend C M δ k ω), C.sizeN i ω)
          ≤ ∑ ω ∈ S2, C.P ω * wcost2 C M δ E bail p' k (j + 1) ω := by
        refine Finset.sum_le_sum fun ω hm => ?_
        rw [hS2_b ω hm, Finset.Ico_self, Finset.sum_empty, mul_zero]
        exact mul_nonneg (le_of_lt (C.hP ω)) (wcost2_nonneg E bail hp0 k (j+1) ω)
      have hS3_fin : ∑ ω ∈ S3, C.P ω *
            (∑ i ∈ Finset.Ico (j + 1) (eend C M δ k ω), C.sizeN i ω)
          ≤ ∑ ω ∈ S3, C.P ω * (p' - pe) := by
        refine Finset.sum_le_sum fun ω hm => ?_
        exact mul_le_mul_of_nonneg_left (htail_le ω (hS_sub ω hm))
          (le_of_lt (C.hP ω))
      linarith [hprem, hIH, hS2_zero, hS3_fin]

end ChargeClaim

section Wrap

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem τ2_isStopping (hMm : M ≤ C.m) {k : ℕ} (hk : k ≤ M) :
    C.IsStopping (τ2 C M δ k) := by
  intro h ω ω' hh
  constructor
  · intro hle
    rw [τ2_congr hMm k hk (show C.hist h ω' = C.hist h ω from hh.symm) hle]
    exact hle
  · intro hle
    rw [τ2_congr hMm k hk (show C.hist h ω = C.hist h ω' from hh) hle]
    exact hle

/-- Away from the forced last window, the effective end is the boundary. -/
theorem eend_eq_τ2 (hMm : M ≤ C.m) {k : ℕ} (hk : k + 2 ≤ M) (ω : C.Ω) :
    eend C M δ k ω = τ2 C M δ (k + 1) ω := by
  unfold eend
  have h1 : τ2 C M δ (k + 1) ω
      ≤ max (τ2 C M δ k ω + 1)
          (trig C δ (C.expTotal - (k + 1) * δ) (τ2 C M δ k ω) ω) := by
    rw [τ2_succ_def, if_neg (by omega)]
    exact min_le_right _ _
  have h2 : trig C δ (C.expTotal - (k + 1) * δ) (τ2 C M δ k ω) ω
      ≤ massStop C δ (τ2 C M δ k ω) ω := trig_le_massStop _ _ ω
  omega

open Classical in
/-- The output conditional cost bound, over the fine boundary atom. -/
theorem wcost2_bound (hMm : M ≤ C.m) (hM0 : 0 < M)
    (hcA0 : 0 ≤ cA) (hδ : 0 < δ) (hcB0 : 0 ≤ cB)
    {p' : ℝ} (hp : pe + (2 * δ + cB) ≤ p') (hpe : 0 ≤ pe)
    (E : EvaderAlgorithm X) (bail : List (Set X) → Bool)
    {k : ℕ} (hk : k + 1 ≤ M) (ω₀ : C.Ω) :
    wsize2 C M δ k ω₀ * C.mass (C.atom (τ2 C M δ k ω₀) ω₀)
      ≤ ∑ ω ∈ C.atom (τ2 C M δ k ω₀) ω₀,
          C.P ω * E.bailCost bail
            (((List.ofFn (fun i : Fin M => wchunk2 C M δ ω (i : ℕ))).take k).flatten)
            (wchunk2 C M δ ω k) p' := by
  set a := τ2 C M δ k ω₀ with ha_def
  have hτmem : ∀ ω ∈ C.atom a ω₀, τ2 C M δ k ω = a := fun ω hm =>
    τ2_congr hMm k (by omega) (C.mem_atom.mp hm) (le_refl a)
  have hL : wsize2 C M δ k ω₀ * C.mass (C.atom a ω₀)
      = ∑ ω ∈ C.atom a ω₀, C.P ω *
          (wmass C (τ2 C M δ k ω) (eend C M δ k ω) ω) := by
    unfold ChunkSystemB.mass
    rw [Finset.mul_sum,
      ← C.sum_atom_mul_condExp
        (fun ω' => wmass C (τ2 C M δ k ω') (eend C M δ k ω') ω') a ω₀]
    refine Finset.sum_congr rfl fun ω hm => ?_
    have he : C.condExp
        (fun ω' => wmass C (τ2 C M δ k ω') (eend C M δ k ω') ω') a ω
        = wsize2 C M δ k ω₀ := by
      unfold wsize2
      exact C.condExp_congr _ (C.mem_atom.mp hm)
    rw [he]
    ring
  have hNBWa : (C.atom a ω₀).filter
      (fun ω => a < eend C M δ k ω ∧ quiet2 bail a a ω) = C.atom a ω₀ := by
    rw [Finset.filter_eq_self]
    intro ω hm
    refine ⟨?_, ?_⟩
    · have h1 : τ2 C M δ k ω < eend C M δ k ω := lt_eend hk hMm ω
      have h2 := hτmem ω hm
      omega
    · intro i hai hia hi
      exact absurd hia (by omega)
  have hclaim := charge2 hMm hM0 hcA0 hδ hcB0 hp hpe E bail hk ω₀ C.m a
    (le_refl a) (by omega)
  rw [hNBWa] at hclaim
  have hwm : ∀ ω ∈ C.atom a ω₀,
      wmass C (τ2 C M δ k ω) (eend C M δ k ω) ω
        = ∑ i ∈ Finset.Ico a (eend C M δ k ω), C.sizeN i ω := by
    intro ω hm
    unfold wmass
    rw [hτmem ω hm]
  have hR : ∀ ω ∈ C.atom a ω₀, wcost2 C M δ E bail p' k a ω
      = E.bailCost bail
          (((List.ofFn (fun i : Fin M => wchunk2 C M δ ω (i : ℕ))).take k).flatten)
          (wchunk2 C M δ ω k) p' := by
    intro ω hm
    have hτω := hτmem ω hm
    have h1 := wchunk2_prefix (C := C) (δ := δ) hMm ω k (by omega)
    rw [hτω] at h1
    unfold wcost2
    rw [h1]
    unfold wchunk2
    rw [hτω]
  rw [hL, Finset.sum_congr rfl fun ω hm => by rw [hwm ω hm]]
  refine le_trans hclaim (le_of_eq ?_)
  exact Finset.sum_congr rfl fun ω hm => by rw [hR ω hm]

/-- The expected output sizes: exactly the expected truncated masses. -/
theorem sum_wsize2 (hMm : M ≤ C.m) {k : ℕ} (hk : k ≤ M) :
    ∑ ω, C.P ω * wsize2 C M δ k ω
      = ∑ ω, C.P ω * wmass C (τ2 C M δ k ω) (eend C M δ k ω) ω := by
  show ∑ ω, C.P ω * C.condExp
      (fun ω' => wmass C (τ2 C M δ k ω') (eend C M δ k ω') ω') (τ2 C M δ k ω) ω = _
  exact ChunkSystemB.sum_stopped_condExp C (τ2_isStopping hMm hk) _

end Wrap

section Loss

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

/-- Once a boundary sits on its cap, all later boundaries chain along. -/
theorem cap_chain (hMm : M ≤ C.m) {k : ℕ} (hk : k + 1 ≤ M - 1) {ω : C.Ω}
    (hcap : τ2 C M δ (k + 1) ω = C.m - (M - (k + 1))) :
    τ2 C M δ (M - 1) ω = C.m - 1 := by
  -- induct on the remaining distance
  suffices h : ∀ d j, j + d = M - 1 → k + 1 ≤ j →
      τ2 C M δ j ω = C.m - (M - j) → τ2 C M δ (M - 1) ω = C.m - 1 by
    exact h (M - 1 - (k + 1)) (k + 1) (by omega) (le_refl _) hcap
  intro d
  induction d with
  | zero =>
    intro j hj _ hcapj
    have hjM : j = M - 1 := by omega
    subst hjM
    rw [hcapj]
    congr 1
    omega
  | succ d ih =>
    intro j hj hkj hcapj
    have hjM : j + 1 ≤ M - 1 := by omega
    refine ih (j + 1) (by omega) (by omega) ?_
    have hMj : ¬ M ≤ j + 1 := by omega
    rw [τ2_succ_def, if_neg hMj, hcapj]
    have hcap1 : C.m - (M - j) + 1 = C.m - (M - (j + 1)) := by omega
    rw [hcap1]
    have h2 : C.m - (M - (j + 1))
        ≤ max (C.m - (M - (j + 1)))
            (trig C δ (C.expTotal - (j + 1) * δ) (C.m - (M - (j + 1))) ω) :=
      le_max_left _ _
    omega

/-- On a lossy path no cap ever binds before the last window. -/
theorem boundary_is_trigger (hMm : M ≤ C.m) (hM0 : 0 < M) {ω : C.Ω}
    (hloss : eend C M δ (M - 1) ω < C.m) {k : ℕ} (hk : k + 1 ≤ M - 1) :
    τ2 C M δ k ω < τ2 C M δ (k + 1) ω
      ∧ (C.condFuture (τ2 C M δ (k + 1) ω) ω ≤ C.expTotal - (k + 1) * δ
        ∨ 2 * δ ≤ wmass C (τ2 C M δ k ω) (τ2 C M δ (k + 1) ω) ω) := by
  have hne : τ2 C M δ (k + 1) ω ≠ C.m - (M - (k + 1)) := by
    intro hcap
    have hchain := cap_chain hMm hk hcap
    have hend : eend C M δ (M - 1) ω = C.m := by
      unfold eend
      rw [hchain, show M - 1 + 1 = M by omega, τ2_last (le_refl M) hM0 ω]
      have h1 : 0 < C.m := by omega
      have hms := massStop_le_m (C := C) (δ := δ) (C.m - 1) ω
      omega
    omega
  have hMk : ¬ M ≤ k + 1 := by omega
  have hdef : τ2 C M δ (k + 1) ω = min (C.m - (M - (k + 1)))
      (max (τ2 C M δ k ω + 1)
        (trig C δ (C.expTotal - (k + 1) * δ) (τ2 C M δ k ω) ω)) := by
    rw [τ2_succ_def, if_neg hMk]
  set a := τ2 C M δ k ω
  set x := C.expTotal - (k + 1) * δ
  have htlem0 := Nat.sInf_mem (⟨C.m, by simp⟩ :
    {h | (a < h ∧ (C.condFuture h ω ≤ x ∨ 2 * δ ≤ wmass C a h ω))
      ∨ h = C.m}.Nonempty)
  simp only [Set.mem_setOf_eq] at htlem0
  have htlem : (a < trig C δ x a ω
      ∧ (C.condFuture (trig C δ x a ω) ω ≤ x
        ∨ 2 * δ ≤ wmass C a (trig C δ x a ω) ω))
      ∨ trig C δ x a ω = C.m := htlem0
  have hlt : a < τ2 C M δ (k + 1) ω := τ2_lt_succ (by omega) hMm ω
  have hcaple : τ2 C M δ (k + 1) ω ≤ C.m - (M - (k + 1)) :=
    τ2_le (by omega) hMm ω
  rcases htlem with ⟨h1, h2⟩ | h1
  · -- real trigger membership
    have htrig_val : τ2 C M δ (k + 1) ω
        = trig C δ x a ω ∨ τ2 C M δ (k + 1) ω = a + 1 := by
      rcases Nat.lt_or_ge (trig C δ x a ω) (a + 1) with h3 | h3
      · right
        show τ2 C M δ (k + 1) ω = a + 1
        have h4 : trig C δ x a ω ≤ a := by omega
        omega
      · rcases Nat.lt_or_ge (C.m - (M - (k + 1)))
          (max (a + 1) (trig C δ x a ω)) with h5 | h5
        · exfalso
          apply hne
          rw [hdef]
          omega
        · left
          rw [hdef]
          omega
    rcases htrig_val with h3 | h3
    · refine ⟨hlt, ?_⟩
      rw [h3]
      exact h2
    · -- forced single step: the trigger must be at a + 1 as well
      have h4 : trig C δ x a ω ≤ a + 1 := by
        by_contra hcon
        push_neg at hcon
        rw [hdef] at h3
        have h5 : max (a + 1) (trig C δ x a ω) = trig C δ x a ω := by omega
        rcases Nat.lt_or_ge (C.m - (M - (k + 1))) (trig C δ x a ω) with h6 | h6
        · apply hne
          rw [hdef]
          omega
        · omega
      have h6 : trig C δ x a ω = a + 1 := by omega
      refine ⟨hlt, ?_⟩
      rw [h3, ← h6]
      exact h2
  · -- trigger is the sentinel: the boundary would sit on its cap
    exfalso
    apply hne
    rw [hdef, h1]
    have h2 : C.m - (M - (k + 1)) ≤ max (a + 1) C.m := by
      have := le_max_right (a + 1) C.m
      omega
    omega

end Loss

section LossBound

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem wmass_total (ω : C.Ω) : wmass C 0 C.m ω = C.totalSize ω := by
  unfold wmass
  rw [← Finset.range_eq_Ico,
    ← Fin.sum_univ_eq_sum_range (fun j => C.sizeN j ω) C.m]
  unfold ChunkSystemB.totalSize
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold ChunkSystemB.sizeN
  rw [dif_pos i.isLt]

theorem wmass_consec {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (ω : C.Ω) :
    wmass C a b ω + wmass C b c ω = wmass C a c ω :=
  Finset.sum_Ico_consecutive _ hab hbc

theorem wmass_nonneg (hcA0 : 0 ≤ cA) (a b : ℕ) (ω : C.Ω) :
    0 ≤ wmass C a b ω :=
  Finset.sum_nonneg fun j _ => C.sizeN_nonneg hcA0 j ω

theorem sum_window_masses (hMm : M ≤ C.m) (ω : C.Ω) {n : ℕ} (hn : n ≤ M) :
    ∑ k ∈ Finset.range n, wmass C (τ2 C M δ k ω) (τ2 C M δ (k + 1) ω) ω
      = wmass C 0 (τ2 C M δ n ω) ω := by
  induction n with
  | zero =>
    rw [Finset.sum_range_zero, τ2_zero]
    unfold wmass
    rw [Finset.Ico_self, Finset.sum_empty]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    refine wmass_consec ?_ ?_ ω
    · have h1 : τ2 C M δ 0 ω ≤ τ2 C M δ n ω := τ2_mono (by omega) (by omega) hMm ω
      rw [τ2_zero] at h1
      exact h1
    · exact le_of_lt (τ2_lt_succ hn hMm ω)

open Classical in
/-- Pointwise loss bound: the mass beyond the effective end of the final
window is controlled by the squared deviation of the total. -/
theorem loss_pointwise (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hT0 : 0 < C.expTotal)
    (hM1 : 2 * C.expTotal + 4 * δ ≤ (M - 1 : ℕ) * δ) (ω : C.Ω) :
    wmass C (eend C M δ (M - 1) ω) C.m ω
      ≤ 2 * (C.totalSize ω - C.expTotal) ^ 2 / C.expTotal := by
  rcases Nat.lt_or_ge (eend C M δ (M - 1) ω) C.m with hloss | hge
  · -- counting on a lossy path
    set D := (Finset.range (M - 1)).filter
      (fun k => C.condFuture (τ2 C M δ (k + 1) ω) ω
        ≤ C.expTotal - (k + 1) * δ) with hD_def
    set Dc := (Finset.range (M - 1)).filter
      (fun k => ¬ C.condFuture (τ2 C M δ (k + 1) ω) ω
        ≤ C.expTotal - (k + 1) * δ) with hDc_def
    have hcards : D.card + Dc.card = M - 1 := by
      rw [hD_def, hDc_def, Finset.filter_card_add_filter_neg_card_eq_card,
        Finset.card_range]
    -- each k in D pins a nonnegative level
    have hD_bound : (D.card : ℝ) * δ ≤ C.expTotal := by
      have hsub : D ⊆ Finset.range (Nat.floor (C.expTotal / δ)) := by
        intro k hk
        rw [hD_def, Finset.mem_filter] at hk
        have hg := C.condFuture_nonneg hcA0 (τ2 C M δ (k + 1) ω) ω
        have hx : ((k : ℝ) + 1) * δ ≤ C.expTotal := by
          have := hk.2
          nlinarith
        have hle : ((k + 1 : ℕ) : ℝ) ≤ C.expTotal / δ := by
          rw [le_div_iff₀ hδ]
          push_cast
          exact hx
        have hfl : k + 1 ≤ Nat.floor (C.expTotal / δ) := Nat.le_floor hle
        rw [Finset.mem_range]
        omega
      have h1 : (D.card : ℝ) ≤ (Nat.floor (C.expTotal / δ) : ℝ) := by
        have h0 := Finset.card_le_card hsub
        rw [Finset.card_range] at h0
        exact_mod_cast h0
      have h2 : (Nat.floor (C.expTotal / δ) : ℝ) ≤ C.expTotal / δ :=
        Nat.floor_le (by positivity)
      have h3 : (D.card : ℝ) ≤ C.expTotal / δ := le_trans h1 h2
      calc (D.card : ℝ) * δ ≤ (C.expTotal / δ) * δ :=
            mul_le_mul_of_nonneg_right h3 (le_of_lt hδ)
        _ = C.expTotal := by field_simp
    -- each k outside D consumed mass at least 2δ
    have hDc_bound : (Dc.card : ℝ) * (2 * δ) ≤ C.totalSize ω := by
      have h1 : ∀ k ∈ Dc, 2 * δ ≤ wmass C (τ2 C M δ k ω) (τ2 C M δ (k + 1) ω) ω := by
        intro k hk
        rw [hDc_def, Finset.mem_filter, Finset.mem_range] at hk
        have hbt := boundary_is_trigger hMm hM0 hloss (k := k) (by omega)
        rcases hbt.2 with h2 | h2
        · exact absurd h2 hk.2
        · exact h2
      calc (Dc.card : ℝ) * (2 * δ)
          = ∑ _k ∈ Dc, 2 * δ := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ k ∈ Dc, wmass C (τ2 C M δ k ω) (τ2 C M δ (k + 1) ω) ω :=
            Finset.sum_le_sum h1
        _ ≤ ∑ k ∈ Finset.range (M - 1),
              wmass C (τ2 C M δ k ω) (τ2 C M δ (k + 1) ω) ω := by
            refine Finset.sum_le_sum_of_subset_of_nonneg
              (by rw [hDc_def]; exact Finset.filter_subset _ _) ?_
            intro k _ _
            exact wmass_nonneg hcA0 _ _ ω
        _ = wmass C 0 (τ2 C M δ (M - 1) ω) ω :=
            sum_window_masses hMm ω (by omega)
        _ ≤ C.totalSize ω := by
            rw [← wmass_total (C := C) ω]
            have h3 : τ2 C M δ (M - 1) ω ≤ C.m := τ2_le_m (by omega) hMm ω
            rw [← wmass_consec (Nat.zero_le _) h3 ω]
            have := wmass_nonneg (C := C) hcA0
              (τ2 C M δ (M - 1) ω) C.m ω
            linarith
    -- combine: the total is large on lossy paths
    have hbig : 2 * C.expTotal ≤ C.totalSize ω := by
      have hMcast : ((M - 1 : ℕ) : ℝ) = (D.card : ℝ) + (Dc.card : ℝ) := by
        exact_mod_cast hcards.symm
      have h1 : ((M - 1 : ℕ) : ℝ) * δ ≤ C.expTotal + C.totalSize ω / 2 := by
        rw [hMcast, add_mul]
        have h2 : (Dc.card : ℝ) * δ ≤ C.totalSize ω / 2 := by linarith
        linarith
      linarith
    -- pointwise inequality on the large-total event
    have hlossle : wmass C (eend C M δ (M - 1) ω) C.m ω ≤ C.totalSize ω := by
      rw [← wmass_total (C := C) ω]
      have h3 : eend C M δ (M - 1) ω ≤ C.m := by omega
      rw [← wmass_consec (Nat.zero_le _) h3 ω]
      have := wmass_nonneg (C := C) hcA0 0
        (eend C M δ (M - 1) ω) ω
      linarith
    have hdev : C.expTotal ≤ C.totalSize ω - C.expTotal := by linarith
    rw [le_div_iff₀ hT0]
    nlinarith [hlossle, hbig, hdev, hT0,
      sq_nonneg (C.totalSize ω - C.expTotal)]
  · -- no loss
    have hempty : Finset.Ico (eend C M δ (M - 1) ω) C.m = ∅ :=
      Finset.Ico_eq_empty (by omega)
    unfold wmass
    rw [hempty, Finset.sum_empty]
    positivity

end LossBound

section Assemble

variable {C : ChunkSystemB X s t cA cB T pe mL} {M : ℕ} {δ : ℝ}

theorem whist2_atom (hMm : M ≤ C.m) {k : ℕ} (hk : k ≤ M) (ω₀ ω : C.Ω) :
    whist2 C M δ k ω = whist2 C M δ k ω₀
      ↔ C.hist (τ2 C M δ k ω₀) ω = C.hist (τ2 C M δ k ω₀) ω₀ := by
  rw [whist2_pair]
  constructor
  · rintro ⟨he, hf⟩
    rw [he] at hf
    exact hf
  · intro hh
    have hτ : τ2 C M δ k ω = τ2 C M δ k ω₀ :=
      τ2_congr hMm k hk hh (le_refl _)
    rw [hτ]
    exact ⟨rfl, hh⟩

theorem whist2_ref' (hMm : M ≤ C.m) (hM0 : 0 < M) {i j : ℕ} (hij : i ≤ j)
    {ω ω' : C.Ω} (hh : whist2 C M δ j ω = whist2 C M δ j ω') :
    whist2 C M δ i ω = whist2 C M δ i ω' := by
  by_cases hjM : j ≤ M
  · exact whist2_ref hMm hij hjM hh
  · push_neg at hjM
    obtain ⟨he, hf⟩ := whist2_pair.mp hh
    have hjω : τ2 C M δ j ω = C.m := τ2_last (by omega) hM0 ω
    rw [hjω] at hf
    by_cases hiM : i ≤ M
    · have hτi : τ2 C M δ i ω ≤ C.m := τ2_le_m hiM hMm ω
      have hτeq : τ2 C M δ i ω' = τ2 C M δ i ω :=
        τ2_congr hMm i hiM (show C.hist C.m ω' = C.hist C.m ω from hf.symm) hτi
      rw [whist2_pair]
      exact ⟨hτeq.symm, C.href _ C.m hτi ω ω' hf⟩
    · push_neg at hiM
      rw [whist2_pair]
      have h1 : τ2 C M δ i ω = C.m := τ2_last (by omega) hM0 ω
      have h2 : τ2 C M δ i ω' = C.m := τ2_last (by omega) hM0 ω'
      rw [h1, h2]
      exact ⟨rfl, hf⟩

open Classical in
theorem sum_wsize2_total (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hT0 : 0 < C.expTotal)
    (hM1 : 2 * C.expTotal + 4 * δ ≤ (M - 1 : ℕ) * δ)
    {V : ℝ} (hVar : ∑ ω, C.P ω * (C.totalSize ω - C.expTotal) ^ 2 ≤ V) :
    C.expTotal - 2 * V / C.expTotal
      ≤ ∑ ω, C.P ω * (∑ k ∈ Finset.range M, wsize2 C M δ k ω) := by
  have h1 : ∑ ω, C.P ω * (∑ k ∈ Finset.range M, wsize2 C M δ k ω)
      = ∑ k ∈ Finset.range M, ∑ ω, C.P ω * wsize2 C M δ k ω := by
    rw [Finset.sum_congr rfl fun ω _ => Finset.mul_sum _ _ _, Finset.sum_comm]
  rw [h1, Finset.sum_congr rfl fun k hk =>
    sum_wsize2 hMm (le_of_lt (Finset.mem_range.mp hk)), Finset.sum_comm]
  have hpart : ∀ ω : C.Ω,
      ∑ k ∈ Finset.range M,
        C.P ω * wmass C (τ2 C M δ k ω) (eend C M δ k ω) ω
      = C.P ω * (C.totalSize ω - wmass C (eend C M δ (M - 1) ω) C.m ω) := by
    intro ω
    rw [← Finset.mul_sum]
    congr 1
    have hsplit : ∑ k ∈ Finset.range M,
        wmass C (τ2 C M δ k ω) (eend C M δ k ω) ω
        = (∑ k ∈ Finset.range (M - 1),
            wmass C (τ2 C M δ k ω) (eend C M δ k ω) ω)
          + wmass C (τ2 C M δ (M - 1) ω) (eend C M δ (M - 1) ω) ω := by
      have hM' : M = M - 1 + 1 := by omega
      have hr : Finset.range M = Finset.range (M - 1 + 1) := by
        rw [← hM']
      conv_lhs => rw [hr]
      rw [Finset.sum_range_succ]
    rw [hsplit, Finset.sum_congr rfl (fun k hk => by
      rw [eend_eq_τ2 hMm (by
        have := Finset.mem_range.mp hk
        omega) ω]),
      sum_window_masses hMm ω (by omega)]
    have hτe : τ2 C M δ (M - 1) ω ≤ eend C M δ (M - 1) ω :=
      le_of_lt (lt_eend (by omega) hMm ω)
    have hem : eend C M δ (M - 1) ω ≤ C.m := by
      have h2 := eend_le (C := C) (M := M) (δ := δ) (k := M - 1) ω
      have h3 : τ2 C M δ (M - 1 + 1) ω ≤ C.m := τ2_le_m (by omega) hMm ω
      omega
    have hc1 := wmass_consec (C := C) (Nat.zero_le (τ2 C M δ (M - 1) ω)) hτe ω
    have hc2 := wmass_consec (C := C)
      (Nat.zero_le (eend C M δ (M - 1) ω)) hem ω
    have hc3 := wmass_total (C := C) ω
    linarith
  rw [Finset.sum_congr rfl fun ω _ => hpart ω]
  have h2 : ∑ ω, C.P ω * (C.totalSize ω - wmass C (eend C M δ (M - 1) ω) C.m ω)
      = C.expTotal - ∑ ω, C.P ω * wmass C (eend C M δ (M - 1) ω) C.m ω := by
    unfold ChunkSystemB.expTotal
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ω _ => by ring
  rw [h2]
  have h3 : ∑ ω, C.P ω * wmass C (eend C M δ (M - 1) ω) C.m ω
      ≤ 2 * V / C.expTotal := by
    calc ∑ ω, C.P ω * wmass C (eend C M δ (M - 1) ω) C.m ω
        ≤ ∑ ω, C.P ω * (2 * (C.totalSize ω - C.expTotal) ^ 2 / C.expTotal) :=
          Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
            (loss_pointwise hMm hM0 hδ hcA0 hT0 hM1 ω) (le_of_lt (C.hP ω))
      _ = (2 / C.expTotal) * ∑ ω, C.P ω * (C.totalSize ω - C.expTotal) ^ 2 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
      _ ≤ (2 / C.expTotal) * V := by
          refine mul_le_mul_of_nonneg_left hVar (by positivity)
      _ = 2 * V / C.expTotal := by ring
  linarith

open Classical in
/-- **Chunk regrouping, v2**: any chunk system regroups into `M` windows of
pointwise sizes in `[0, 2δ + cB]` serving the same request sequence, at
escape price `pe + 2δ + cB`, preserving the expected total up to a loss
controlled by the variance of the total. No jump or monotonicity
hypotheses. -/
theorem chunk_regroup (C : ChunkSystemB X s t cA cB T pe mL)
    {M : ℕ} {δ V T' p' : ℝ}
    (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hpe : 0 ≤ pe)
    (hp : pe + (2 * δ + cB) ≤ p')
    (hT0 : 0 < C.expTotal)
    (hM1 : 2 * C.expTotal + 4 * δ ≤ (M - 1 : ℕ) * δ)
    (hVar : ∑ ω, C.P ω * (C.totalSize ω - C.expTotal) ^ 2 ≤ V)
    (hT' : T' ≤ C.expTotal - 2 * V / C.expTotal) :
    Nonempty (ChunkSystemB X s t 0 (2 * δ + cB) T' p' M) := by
  refine ⟨{
    Ω := C.Ω
    instFin := C.instFin
    instDec := C.instDec
    P := C.P
    m := M
    hist := fun n ω => whist2 C M δ n ω
    chunk := fun ω k => wchunk2 C M δ ω (k : ℕ)
    size := fun ω k => wsize2 C M δ (k : ℕ) ω
    hP := C.hP
    hPsum := C.hPsum
    hm := le_refl M
    hm0 := hM0
    href := fun i j hij ω ω' hh => whist2_ref' hMm hM0 hij hh
    hadapt := fun k ω ω' hh => wchunk2_congr hMm k.isLt hh
    hsmeas := fun k ω ω' hh => wsize2_congr hMm hh
    hne := fun ω k => wchunk2_ne ω (k : ℕ)
    hlast := ?_
    hopt := ?_
    hsize := ?_
    hcost := ?_
    htotal := ?_ }⟩
  · intro ω
    rw [wchunk2_flatten hMm hM0 ω]
    exact C.hlast ω
  · intro ω
    rw [wchunk2_flatten hMm hM0 ω]
    exact C.hopt ω
  · intro ω k
    exact ⟨wsize2_nonneg hcA0 (k : ℕ) ω, wsize2_le hMm hδ hcB0 k.isLt ω⟩
  · intro k ω₀ E bail
    have hfilter : Finset.univ.filter
        (fun ω => whist2 C M δ (k : ℕ) ω = whist2 C M δ (k : ℕ) ω₀)
        = C.atom (τ2 C M δ (k : ℕ) ω₀) ω₀ := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [whist2_atom hMm (le_of_lt k.isLt) ω₀ ω, C.mem_atom]
    rw [hfilter]
    exact wcost2_bound hMm hM0 hcA0 hδ hcB0 hp hpe E bail k.isLt ω₀
  · have h1 := sum_wsize2_total hMm hM0 hδ hcA0 hT0 hM1 hVar
    calc T' ≤ C.expTotal - 2 * V / C.expTotal := hT'
      _ ≤ ∑ ω, C.P ω * (∑ k ∈ Finset.range M, wsize2 C M δ k ω) := h1
      _ = ∑ ω, C.P ω * (∑ k : Fin M, wsize2 C M δ (k : ℕ) ω) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          rw [Fin.sum_univ_eq_sum_range (fun k => wsize2 C M δ k ω) M]

end Assemble

end Combine2

namespace KServer

/-- Platform-facing restatement with expectations spelled out. -/
theorem chunk_regroup {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : ChunkSystemB X s t cA cB T pe mL)
    {M : ℕ} {δ V T' p' : ℝ}
    (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hpe : 0 ≤ pe)
    (hp : pe + (2 * δ + cB) ≤ p')
    (hT0 : 0 < ∑ ω, C.P ω * ∑ i, C.size ω i)
    (hM1 : 2 * (∑ ω, C.P ω * ∑ i, C.size ω i) + 4 * δ ≤ (M - 1 : ℕ) * δ)
    (hVar : ∑ ω, C.P ω *
      ((∑ i, C.size ω i) - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hT' : T' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i)
      - 2 * V / (∑ ω, C.P ω * ∑ i, C.size ω i)) :
    Nonempty (ChunkSystemB X s t 0 (2 * δ + cB) T' p' M) :=
  Combine2.chunk_regroup C hMm hM0 hδ hcA0 hcB0 hpe hp hT0 hM1 hVar hT'

end KServer

theorem solution {X : Type*} [MetricSpace X] {s t : X}
    {cA cB T pe : ℝ} {mL : ℕ} (C : KServer.ChunkSystemB X s t cA cB T pe mL)
    {M : ℕ} {δ V T' p' : ℝ}
    (hMm : M ≤ C.m) (hM0 : 0 < M) (hδ : 0 < δ)
    (hcA0 : 0 ≤ cA) (hcB0 : 0 ≤ cB) (hpe : 0 ≤ pe)
    (hp : pe + (2 * δ + cB) ≤ p')
    (hT0 : 0 < ∑ ω, C.P ω * ∑ i, C.size ω i)
    (hM1 : 2 * (∑ ω, C.P ω * ∑ i, C.size ω i) + 4 * δ ≤ (M - 1 : ℕ) * δ)
    (hVar : ∑ ω, C.P ω *
      ((∑ i, C.size ω i) - ∑ ω', C.P ω' * ∑ i, C.size ω' i) ^ 2 ≤ V)
    (hT' : T' ≤ (∑ ω, C.P ω * ∑ i, C.size ω i)
      - 2 * V / (∑ ω, C.P ω * ∑ i, C.size ω i)) :
    Nonempty (KServer.ChunkSystemB X s t 0 (2 * δ + cB) T' p' M) :=
  KServer.chunk_regroup C hMm hM0 hδ hcA0 hcB0 hpe hp hT0 hM1 hVar hT'
