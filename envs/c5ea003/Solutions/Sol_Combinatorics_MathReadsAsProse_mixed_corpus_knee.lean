-- Prove2me | solution 1 for Combinatorics.MathReadsAsProse.mixed_corpus_knee
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:36:52.970711+00:00
-- url     : https://prove2.me/submissions/198a352b-7334-4976-b448-0f70fccfe64a

-- Sol generated from Combinatorics/MathReadsAsProse.lean
import Mathlib
import Definitions.Def_Combinatorics_KneeInvariance
import Definitions.Def_Combinatorics_MathReadsAsProse
import Theorems.Thm_Combinatorics_KneeInvariance_agree_gate_reachable
import Theorems.Thm_Combinatorics_KneeInvariance_agree_mono
import Theorems.Thm_Combinatorics_KneeInvariance_flat_agree_of_ge
import Theorems.Thm_Combinatorics_KneeInvariance_flat_knee
import Theorems.Thm_Combinatorics_KneeInvariance_knee_mix_le_max
import Theorems.Thm_Combinatorics_KneeInvariance_min_le_knee_mix
import Theorems.Thm_Combinatorics_KneeInvariance_ofCountProfile_agree
import Theorems.Thm_Combinatorics_KneeInvariance_ofCountProfile_knee

/-!
# MATH-READS-AS-PROSE: the measured NET-70 instance

This file instantiates the abstract theory of `Combinatorics.KneeInvariance` on
the **measured NET-70 sweep** and derives the verdict formally.

Measured data (Qwen-class model, exact gate, 24 windows per cell, deterministic
harness; the harness is byte-identical across domains, only the text changes):

| ctx  | domain | sweep (budget ↦ retained agreement)                              | full acc |
|------|--------|------------------------------------------------------------------|----------|
| 512  | math   | 4 ↦ .907, 8 ↦ .959, 12 ↦ .979, 16 ↦ .987, 20 ↦ .989, 24 ↦ .988   | .3262    |
| 512  | prose  | knee at 16 (NET-6x)                                              | .4460    |
| 1024 | math   | 8 ↦ .952, 12 ↦ .965, 16 ↦ .978, 20 ↦ .983, 24+ ↦ pass            | .3418    |
| 1024 | prose  | knee at 20 (NET-6x)                                              | .4612    |

Two modelling decisions, both stated explicitly:

* the sweep is read as a **monotone step count profile** on `n = 10000`
  windows — the measured `24 ↦ .988` at ctx 512 sits below `20 ↦ .989` by one
  unit in the third decimal, i.e. inside the reported standard error, so the
  monotone hull (`.989` from 20 on) is used;
* at `k = ctx` the truncated model *is* the full model, so the profile
  saturates at `1` there.  This is what makes every gate `≤ 1` reachable.

Everything else is derived.  In particular the knees are *computed*, not
assumed: `math512_knee = 16` and `math1024_knee = 20`, for **every** gate in the
measured admissible windows `(0.979, 0.987]` and `(0.978, 0.983]`.  Those
windows overlap in `(0.979, 0.983]`, so one single gate certifies both cells and
the ctx increment is exactly `+4` (NET-67 shape preservation).

The verdict theorems are `math_reads_as_prose_512`, `math_reads_as_prose_1024`
(P3: identical knees with a 12-point accuracy gap), `net70_P1_refuted`
(harder text does not need more keys) and `three_domain_deployment_table`
(prose and math share one deployment entry; only code shifts).
-/

open Combinatorics.MathReadsAsProse

open Finset Combinatorics.KneeInvariance

/-! ## The measured count profiles -/



theorem mathT512_mono : Monotone mathT512 := by
  intro a b hab
  unfold mathT512
  split_ifs <;> omega


theorem mathT512_le (k : ℕ) : mathT512 k ≤ 10000 := by
  unfold mathT512; split_ifs <;> omega


theorem mathT512_sat : ∃ K, mathT512 K = 10000 := ⟨512, by unfold mathT512; norm_num⟩


theorem mathT512_below_knee {b : ℕ} (hb : b < 16) : mathT512 b ≤ 9790 := by
  unfold mathT512; split_ifs <;> omega

theorem mathT512_at_knee : mathT512 16 = 9870 := by unfold mathT512; norm_num



/-! ## The measured workloads -/






/-! ## The knees are computed, over the whole admissible gate window -/

/-- **Math ctx 512: the knee is exactly 16**, for every gate in the measured
admissible window `(0.979, 0.987]`.  The gate is not tuned: the whole interval
between the failing `12`-sweep value and the passing `16`-value certifies it. -/
theorem math512_knee {g : ℚ} (hlo : (979 : ℚ) / 1000 < g) (hhi : g ≤ (987 : ℚ) / 1000) :
    knee mathWorkload512.agree g = 16 := by
  refine ofCountProfile_knee mathT512_mono mathT512_le mathT512_sat 3262 (by norm_num)
    ?_ ?_
  · rw [mathT512_at_knee]; push_cast; linarith
  · intro b hb
    have h := mathT512_below_knee hb
    have hb' : (mathT512 b : ℚ) ≤ 9790 := by exact_mod_cast h
    push_cast
    linarith




theorem prose512_knee {g : ℚ} (h0 : 0 < g) (h1 : g ≤ 1) :
    knee proseWorkload512.agree g = 16 := flat_knee (by norm_num) h0 h1





/-! ## The verdict -/





/-! ## The three-domain deployment table -/








open Combinatorics.MathReadsAsProse in
theorem solution{theta g : ℚ} (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (hlo : (979 : ℚ) / 1000 < g) (hhi : g ≤ (987 : ℚ) / 1000) :
    knee (mixCurve theta proseWorkload512.agree mathWorkload512.agree) g = 16 := by
  have hg0 : 0 < g := by linarith
  have hg1 : g ≤ 1 := by linarith
  have hP : ∃ m, g ≤ proseWorkload512.agree m :=
    agree_gate_reachable _ (by norm_num) hg1
  have hM : ∃ m, g ≤ mathWorkload512.agree m :=
    agree_gate_reachable _ (by norm_num) hg1
  have hup : knee (mixCurve theta proseWorkload512.agree mathWorkload512.agree) g ≤ 16 := by
    have := knee_mix_le_max (agree_mono proseWorkload512) (agree_mono mathWorkload512)
      h0 h1 hP hM (g := g)
    rwa [prose512_knee hg0 hg1, math512_knee hlo hhi, max_self] at this
  have hne : ∃ m, g ≤ mixCurve theta proseWorkload512.agree mathWorkload512.agree m := by
    refine ⟨10000, ?_⟩
    have hp : proseWorkload512.agree 10000 = 1 := flat_agree_of_ge (by norm_num) (by norm_num)
    have hm : mathWorkload512.agree 10000 = 1 := by
      unfold mathWorkload512
      rw [ofCountProfile_agree mathT512_mono mathT512_le mathT512_sat]
      norm_num [mathT512]
    simp only [mixCurve, hp, hm]
    linarith
  have hlow : 16 ≤ knee (mixCurve theta proseWorkload512.agree mathWorkload512.agree) g := by
    have := min_le_knee_mix (A := proseWorkload512.agree) (B := mathWorkload512.agree)
      h0 h1 hne
    rwa [prose512_knee hg0 hg1, math512_knee hlo hhi, min_self] at this
  omega
