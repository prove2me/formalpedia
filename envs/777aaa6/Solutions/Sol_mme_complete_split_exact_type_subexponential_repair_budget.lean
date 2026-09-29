-- Prove2me | solution 1 for mme_complete_split_exact_type_subexponential_repair_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T05:00:14.195722+00:00
-- url     : https://prove2.me/submissions/38b75c7e-2cc2-42e8-875c-05e5ded80900

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

open Filter MME MME.CompleteSplit MME.DWZComponentRestriction
open scoped BigOperators Classical

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

private theorem exact_type_card_le (ell N : ℕ) (beta : Profile ell) :
    Fintype.card {w : PowIndex (CompleteWord ell) N // ApproxConsistent id beta 0 w} ≤
      3 ^ ((2 ^ (ell - 1)) * N) := by
  classical
  calc
    _ ≤ Fintype.card (PowIndex (CompleteWord ell) N) := Fintype.card_subtype_le _
    _ = Fintype.card (Fin N → CompleteWord ell) :=
      Fintype.card_congr (PowIndex.equivFun _ N)
    _ = _ := by simp [CompleteWord, ← pow_mul]

private theorem repair_depth_eventually (C : ℕ) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ N : ℕ in atTop, ∃ h : ℕ,
      3 ^ (C * N) < (2 * N) ^ h ∧
      Real.log ((8 ^ h : ℕ) : ℝ) < delta * N := by
  have h8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  have hn : Tendsto (fun N : ℕ ↦ (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have htwon : Tendsto (fun N : ℕ ↦ 2 * (N : ℝ)) atTop atTop :=
    hn.const_mul_atTop (by norm_num)
  have hlog := Real.tendsto_log_atTop.comp htwon
  have hscale : Tendsto (fun N : ℕ ↦ delta * (N : ℝ)) atTop atTop :=
    hn.const_mul_atTop hdelta
  filter_upwards [eventually_ge_atTop 1,
    hlog.eventually (eventually_gt_atTop (2 * (C : ℝ) * Real.log 3 * Real.log 8 / delta)),
    hscale.eventually (eventually_gt_atTop (2 * Real.log 8))] with N hN hlarge hsmall
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hbase : 0 < Real.log (2 * (N : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * N by omega))
  let x : ℝ := delta * (N : ℝ) / (2 * Real.log 8)
  let h : ℕ := Nat.ceil x
  have hx : 0 < x := by dsimp [x]; positivity
  have hlo : x ≤ (h : ℝ) := Nat.le_ceil x
  have hhi : (h : ℝ) < x + 1 := Nat.ceil_lt_add_one hx.le
  have hstrict : ((C * N : ℕ) : ℝ) * Real.log 3 <
      (h : ℝ) * Real.log (2 * (N : ℝ)) := by
    calc
      _ = x * (2 * (C : ℝ) * Real.log 3 * Real.log 8 / delta) := by
        dsimp [x]
        push_cast
        field_simp
      _ < x * Real.log (2 * (N : ℝ)) := mul_lt_mul_of_pos_left hlarge hx
      _ ≤ _ := mul_le_mul_of_nonneg_right hlo hbase.le
  refine ⟨h, ?_, ?_⟩
  · have hr : ((3 ^ (C * N) : ℕ) : ℝ) < (((2 * N) ^ h : ℕ) : ℝ) := by
      apply (Real.log_lt_log_iff (by positivity) (by positivity)).1
      simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul, Real.log_pow] using hstrict
    exact_mod_cast hr
  · have hcost : (h : ℝ) * Real.log 8 < (x + 1) * Real.log 8 :=
      mul_lt_mul_of_pos_right hhi h8
    have hx8 : x * Real.log 8 = delta * (N : ℝ) / 2 := by
      dsimp [x]
      field_simp
    have hb : (h : ℝ) * Real.log 8 < delta * (N : ℝ) := by
      nlinarith
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using hb

/-- Correct complete-word cardinality and a subexponential finite repair-copy budget. -/
theorem solution (ell : ℕ) :
    (∀ (N : ℕ) (beta : Fin 3 → Profile ell),
      (∏ i : Fin 3,
        Fintype.card {w : PowIndex (CompleteWord ell) N //
          ApproxConsistent id (beta i) 0 w}) ≤
        3 ^ (3 * (2 ^ (ell - 1)) * N)) ∧
    ∀ delta : ℝ, 0 < delta → ∀ᶠ N : ℕ in atTop,
      ∃ h : ℕ,
        (∀ beta : Fin 3 → Profile ell,
          (∏ i : Fin 3,
            Fintype.card {w : PowIndex (CompleteWord ell) N //
              ApproxConsistent id (beta i) 0 w}) < (2 * N) ^ h) ∧
        Real.log ((8 ^ h : ℕ) : ℝ) < delta * N := by
  classical
  have hcard (N : ℕ) (beta : Fin 3 → Profile ell) :
      (∏ i : Fin 3,
        Fintype.card {w : PowIndex (CompleteWord ell) N //
          ApproxConsistent id (beta i) 0 w}) ≤
        3 ^ (3 * (2 ^ (ell - 1)) * N) := by
    calc
      _ ≤ ∏ _i : Fin 3, 3 ^ ((2 ^ (ell - 1)) * N) := by
        exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
          (fun i _ ↦ exact_type_card_le ell N (beta i))
      _ = _ := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
        congr 1
        ring
  refine ⟨hcard, ?_⟩
  intro delta hdelta
  filter_upwards [repair_depth_eventually (3 * (2 ^ (ell - 1))) delta hdelta]
    with N hN
  obtain ⟨h, hbound, hcost⟩ := hN
  exact ⟨h, fun beta ↦ (hcard N beta).trans_lt hbound, hcost⟩
