-- Prove2me | Theorems.Thm_erdos257_irrational_support_series_of_tail
-- name    : erdos257_irrational_support_series_of_tail
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T02:53:34.908445+00:00
-- url     : https://prove2.me/theorems/26a05c39-b6fa-47d2-9e35-5a39a8185a03
-- title:
--   Irrationality survives adding a finite support prefix
-- statement:
--   For any integer base b at least two, if the reciprocal Mersenne subseries on the part of a support A strictly above a cutoff B is irrational, then the subseries on all of A is irrational. The omitted finite prefix has a rational sum. No weighted-host hypothesis is needed for this transfer.
-- source:
--   Native extraction of the pinned finite-prefix transfer proved in Will Cook’s Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/CertificateKernel.lean#L9390-L9472 . This hosted proof inlines the source’s pointwise split and rational-prefix steps and imports the already public summability theorem: https://prove2.me/theorems/8d9dc08e-38b2-47aa-adb0-65a6937cb3e4 . Related #257 paper by Will Cook (CC-BY-4.0), with AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex .

import Definitions.Def_Erdos249257_CertificateKernel
import Mathlib

theorem erdos257_irrational_support_series_of_tail (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (B : ℕ)
    (hTail : Irrational
      (Erdos249257.erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n})) :
    Irrational (Erdos249257.erdosSupportSeries b A) := by sorry
