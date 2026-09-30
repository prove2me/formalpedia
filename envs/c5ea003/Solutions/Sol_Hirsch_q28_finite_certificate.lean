-- Prove2me | solution 1 for Hirsch.q28_finite_certificate
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T23:07:58.041987+00:00
-- url     : https://prove2.me/submissions/20dd5ac7-13f4-4a5e-af79-adaea1297309

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert
import Theorems.Thm_Hirsch_q28_chamber_basis_certificate
import Theorems.Thm_Hirsch_q28_quotient_lipschitz

open scoped RealInnerProductSpace
open Hirsch

theorem solution :
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      4 ≤ commonActiveCard o1 o2 s → o1 = o2 ∨ QuotientAdj o1 o2) ∧
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      1 < max (orbitLevel o1) (orbitLevel o2) -
            min (orbitLevel o1) (orbitLevel o2) →
        commonActiveCard o1 o2 s ≤ 3) ∧
    (∀ i j : Fin 20, QuotientAdj i j → orbitLevel j ≤ orbitLevel i + 1) ∧
    (∀ o : Fin 20, ∀ s : Fin 16, ∀ i : Fin 28,
      (tightMask o s).testBit i.val = true ↔
        intDotFlip o s i = orbitDen o) ∧
    (∀ r : ℕ, r < 2002 → certOkUnrank r = true) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) := by
  obtain ⟨hcerts, hunrank, hranklt⟩ := q28_chamber_basis_certificate
  obtain ⟨hfour, hgap, hLev, hmask⟩ := q28_quotient_lipschitz
  exact ⟨hfour, hgap, hLev, hmask, hcerts, hunrank, hranklt⟩
