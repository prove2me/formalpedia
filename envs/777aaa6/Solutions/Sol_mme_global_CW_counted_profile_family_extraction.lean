-- Prove2me | solution 1 for mme_global_CW_counted_profile_family_extraction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:05:56.739634+00:00
-- url     : https://prove2.me/submissions/97721017-2952-4f66-b3c9-4d71566adec2

import Definitions.Def_mme_global_CW_counted_stage
import Definitions.Def_mme_global_CW_joint_start_data
import Theorems.Thm_mme_global_CW_counted_stage_realization
import Theorems.Thm_mme_global_CW_counted_log_copy_bound
import Theorems.Thm_mme_global_CW_part_extraction
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
universe u

theorem solution {K : Type u} [Field K] {M ell types : ℕ} (T : Predicate M)
    (steps : Fin types → CountedStage ell M) (rate : ℝ) (hrate : 0 ≤ rate)
    (hbudget : ∀ j, rate ≤ (steps j).certifiedLogCopies)
    (inside : ∀ j i x, (steps j).output i x → T i x)
    (cover : ∀ x : Fin 3 → FineWord M, supported x → (∀ i, T i (x i)) →
      ∃! j, ∀ i, (steps j).output i (x i)) :
    ∃ D : GlobalCW.Part M ell T, D.inputs = types ∧ D.rate = rate ∧
      Restrict (bigAdd (fun _ : Fin ⌈Real.exp rate⌉₊ ↦ tensor K T))
        (bigAdd (fun _ : Fin types ↦ tensor K (fun _ (_ : FineWord M) ↦ True))) := by
  classical
  choose E hEbudget hEoutput hElower hEexponent using
    (fun j ↦ mme_global_CW_counted_stage_realization (steps j))
  have hcopies (j : Fin types) : ⌈Real.exp rate⌉₊ ≤ (E j).copies :=
    mme_global_CW_counted_log_copy_bound (steps j) (E j) (hElower j) (hEexponent j)
      rate hrate (hbudget j)
  have hmul (j : Fin types) : ⌈Real.exp rate⌉₊ * 8 ^ (E j).repairExponent ≤
      ⌈(E j).hash.lower⌉₊ := (Nat.le_div_iff_mul_le (by positivity)).mp (hcopies j)
  let D : GlobalCW.Part M ell T := .exact types rate hrate E hEbudget hmul
    (fun j i x hx ↦ inside j i x (by simpa only [hEoutput j] using hx))
    (by intro x hx hT; simpa only [hEoutput] using cover x hx hT)
  exact ⟨D,rfl,rfl,mme_global_CW_part_extraction D⟩
