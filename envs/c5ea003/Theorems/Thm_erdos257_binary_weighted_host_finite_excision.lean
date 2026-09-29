-- Prove2me | Theorems.Thm_erdos257_binary_weighted_host_finite_excision
-- name    : erdos257_binary_weighted_host_finite_excision
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T02:23:31.687977+00:00
-- url     : https://prove2.me/theorems/617fa7c2-841e-4ab0-9f2c-7152d79e3891
-- title:
--   Finite deletion preserves all-base irrationality for a binary-weighted host
-- statement:
--   If an infinite set H of positive exponents has a finite-prime weighted summability witness at base two, deleting any finite set F of exponents leaves an irrational reciprocal Mersenne subseries at every integer base b at least two. The deleted exponents need not belong to H.
-- source:
--   New finite-excision consequence of the reviewed #257 paper-theorem wrapper, composed from Will Cook’s Theorem 1. Main theorem: https://prove2.me/theorems/f6d332dc-466f-4f2a-a207-6b0455c0fbbd . Source paper (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L54-L75 . The paper discloses substantial AI-assisted research and drafting: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188 .

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Mathlib

theorem erdos257_binary_weighted_host_finite_excision
    (H F : Set ℕ) (hH0 : 0 ∉ H) (hHInf : H.Infinite)
    (hWeighted : ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 H)
    (hF : F.Finite) :
    ∀ b : ℕ, 2 ≤ b →
      Irrational (Erdos249257.erdosSupportSeries b (H \ F)) := by sorry
