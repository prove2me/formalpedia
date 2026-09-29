-- Prove2me | solution 1 for KServer.bcrLevel2_taut
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-05T14:18:37.901185+00:00
-- url     : https://prove2.me/submissions/41a113a6-e2af-406a-b77f-393f9751d293

import Mathlib
import Definitions.Def_KServer_chunk_system
import Definitions.Def_KServer_cycle_glue
import Definitions.Def_KServer_bcr_space
import Definitions.Def_KServer_glue2
import Definitions.Def_KServer_theta_dists
import Definitions.Def_KServer_race_geo
import Definitions.Def_KServer_bcr_space2

open KServer

theorem solution (β : ℕ) (hβ : 0 < β) (w : ℕ) (x : (bcrLevel2 β hβ w).carrier) :
    dist (bcrLevel2 β hβ w).s x + dist x (bcrLevel2 β hβ w).t
      = dist (bcrLevel2 β hβ w).s (bcrLevel2 β hβ w).t := by
  induction w with
  | zero =>
    letI := pathMetric β
    show dist (0 : Fin (β + 1)) x + dist x (Fin.last β)
      = dist (0 : Fin (β + 1)) (Fin.last β)
    have h1 : dist (0 : Fin (β + 1)) x = |((0 : Fin (β + 1)).val : ℝ) - (x.val : ℝ)| := rfl
    have h2 : dist x (Fin.last β) = |((x.val : ℝ)) - ((Fin.last β).val : ℝ)| := rfl
    have h3 : dist (0 : Fin (β + 1)) (Fin.last β)
        = |((0 : Fin (β + 1)).val : ℝ) - ((Fin.last β).val : ℝ)| := rfl
    have hx : (x.val : ℝ) ≤ (β : ℝ) := by
      have : x.val ≤ β := Nat.lt_succ_iff.mp x.isLt
      exact_mod_cast this
    have hx0 : (0 : ℝ) ≤ (x.val : ℝ) := Nat.cast_nonneg _
    rw [h1, h2, h3]
    simp only [Fin.val_zero, Fin.val_last, Nat.cast_zero, zero_sub]
    rw [abs_neg, abs_of_nonneg hx0, abs_of_nonpos (by linarith), abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤ (β : ℝ) by positivity)]
    ring
  | succ w ih =>
    set L := bcrLevel2 β hβ w with hL
    letI := L.metric
    letI := ThetaChain.stepMetric L.s L.t L.hst
    exact ThetaChain.step_taut L.s L.t L.hst ih x
