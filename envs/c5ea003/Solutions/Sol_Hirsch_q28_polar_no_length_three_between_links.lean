-- Prove2me | solution 1 for Hirsch.q28_polar_no_length_three_between_links
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T23:01:09.207685+00:00
-- url     : https://prove2.me/submissions/abaf4381-e162-4571-93dd-8f53f9d92708

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert
import Theorems.Thm_Hirsch_q28_finite_certificate
import Theorems.Thm_Hirsch_q28_polar_orbit_identification

open scoped RealInnerProductSpace
open Set Hirsch

theorem solution :
    ∀ x y : EuclideanSpace ℝ (Fin 5),
      ¬ (Adj (Hpoly q28A q28B) q28U x ∧
          Adj (Hpoly q28A q28B) y q28V ∧
          ∃ w : ℕ → EuclideanSpace ℝ (Fin 5),
            w 0 = x ∧ w 3 = y ∧
              ∀ j < 3, w j = w (j + 1) ∨
                Adj (Hpoly q28A q28B) (w j) (w (j + 1))) := by
  intro x y ⟨hUx, hyV, w, hw0, hw3, hw⟩
  obtain ⟨_, _, hLev, _, _, _, _⟩ := q28_finite_certificate
  obtain ⟨_, hadjorb, huniq, hU, hV, hUf, hVf⟩ :=
    q28_polar_orbit_identification
  obtain ⟨oU, ox, sU, sx, hUeq, hxeq, hUo⟩ := hadjorb q28U x hUx
  obtain ⟨oy, oV, sy, sV, hyeq, hVeq, hyo⟩ := hadjorb y q28V hyV
  have oU1 : oU = 1 := huniq q28U oU 1 sU 0 hUeq hU
  have oV0 : oV = 0 := huniq q28V oV 0 sV 0 hVeq hV
  have oxne : ox ≠ 1 := by
    intro h
    have hx1 : x = flipPoint sx (orbitPoint 1) := by simpa [h] using hxeq
    have : x = q28U := by simpa [hUf sx] using hx1
    exact hUx.1 this.symm
  have oyne : oy ≠ 0 := by
    intro h
    have hy0 : y = flipPoint sy (orbitPoint 0) := by simpa [h] using hyeq
    have : y = q28V := by simpa [hVf sy] using hy0
    exact hyV.1 this
  have hxadj : QuotientAdj 1 ox := by
    rw [oU1] at hUo
    exact hUo.resolve_left (fun heq => oxne heq.symm)
  have hyadj : QuotientAdj oy 0 := by
    rw [oV0] at hyo
    exact hyo.resolve_left oyne
  have walk_lab : ∀ N, N ≤ 3 →
      ∃ o : Fin 20, ∃ s : Fin 16,
        w N = flipPoint s (orbitPoint o) ∧
        orbitLevel o ≤ orbitLevel ox + N := by
    intro N
    induction N with
    | zero =>
        intro _
        refine ⟨ox, sx, ?_, by omega⟩
        simpa [hw0] using hxeq
    | succ N ih =>
        intro hN
        obtain ⟨oN, sN, hNlab, hNlev⟩ := ih (Nat.le_of_succ_le hN)
        have hstep := hw N (Nat.lt_of_succ_le hN)
        rcases hstep with heq | hadj
        · refine ⟨oN, sN, ?_, ?_⟩
          · rw [← heq]; exact hNlab
          · omega
        · obtain ⟨oa, ob, sa, sb, ha, hb, hrel⟩ := hadjorb (w N) (w (N + 1)) hadj
          have hoa : oa = oN := huniq (w N) oa oN sa sN ha hNlab
          refine ⟨ob, sb, hb, ?_⟩
          rcases hrel with heqO | hadjQ
          · have : orbitLevel ob = orbitLevel oN := by rw [← hoa, heqO]
            omega
          · have hlip := hLev oa ob hadjQ
            have : orbitLevel ob ≤ orbitLevel oN + 1 := by
              simpa [hoa] using hlip
            omega
  obtain ⟨o3, s3, hy3, hlev3⟩ := walk_lab 3 le_rfl
  have o3y : o3 = oy :=
    huniq y o3 oy s3 sy (by simpa [hw3] using hy3) hyeq
  have hpos : orbitLevel (1 : Fin 20) = 0 := rfl
  have hneg : orbitLevel (0 : Fin 20) = 6 := rfl
  have hxlev := hLev 1 ox hxadj
  have hylev := hLev oy 0 hyadj
  rw [hpos] at hxlev
  rw [hneg] at hylev
  rw [o3y] at hlev3
  omega
