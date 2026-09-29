-- Prove2me | Theorems.Thm_mme_dwz_q6_121_211_common_halving_disallowed_word_mismatches_halves
-- name    : mme_dwz_q6_121_211_common_halving_disallowed_word_mismatches_halves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:48:52.091372+00:00
-- url     : https://prove2.me/theorems/f7492c4a-fcb4-4c6e-b790-f4147a5a452d
-- title:
--   Rows 121/211: a disallowed source word mismatches both common-halving profiles
-- statement:
--   Fix Table-2 row 121 or 211 at scale $m$, and let an exact primary $q=6$ hash family use one common balanced splitting of its $2N$ coordinates into two halves of length $N$. Suppose the canonical row-basis decoder identifies the row word's left split grade with the binary grade of the corresponding coupled coordinate.
--
--   If a length-$N$ row word fails the prescribed Table-2 histogram, then it differs in at least one coordinate from the mode-zero profile of every retained address on the first half. The same word also differs in at least one coordinate from the mode-one profile of every retained address on the second half.
--
--   This is the exact support bridge needed to turn the common-halving profile equations into annihilation of every forbidden row basis word after the 121/211 source router.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definitions 5.3-5.4 and the 121/211 split profiles in Section 6.3/Table 2; elementary equality of finite histograms.

import Definitions.Def_mme_CW_q6_common_paired_halving
import Theorems.Thm_mme_dwz_component_disallowed_word_mismatches_profile
import Theorems.Thm_mme_dwz_q6_121_211_component_even_length

open MME MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_121_211_common_halving_disallowed_word_mismatches_halves
    {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = MME.DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6))
    (hcoord : ∀ p,
      p.leftGrade =
        Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
          (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)) :
    let labelGrade : LiftedCoarsePair.{u} 6 1 → Fin 3 :=
      fun p ↦ Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
        (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)
    (∀ (w : PowIndex (LiftedCoarsePair.{u} 6 1) N),
      (¬ ∀ a : Fin 3,
        Fintype.card {r : Fin N //
          (PowIndex.get N w r).leftGrade = a} =
            MME.DWZTable2Counts.split s a * m) →
      ∀ p : Fin A × Fin H,
        ∃ r : Fin N,
          labelGrade (PowIndex.get N w r) ≠
            (family.entry p).1 0 (halving.position (Sum.inl r))) ∧
    (∀ (w : PowIndex (LiftedCoarsePair.{u} 6 1) N),
      (¬ ∀ a : Fin 3,
        Fintype.card {r : Fin N //
          (PowIndex.get N w r).leftGrade = a} =
            MME.DWZTable2Counts.split s a * m) →
      ∀ p : Fin A × Fin H,
        ∃ r : Fin N,
          labelGrade (PowIndex.get N w r) ≠
            (family.entry p).1 1 (halving.position (Sum.inr r))) := by
  sorry
