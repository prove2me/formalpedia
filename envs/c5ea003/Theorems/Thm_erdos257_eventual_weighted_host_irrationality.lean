-- Prove2me | Theorems.Thm_erdos257_eventual_weighted_host_irrationality
-- name    : erdos257_eventual_weighted_host_irrationality
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T02:54:48.3278+00:00
-- url     : https://prove2.me/theorems/f64da58c-9d9e-4d42-bff7-0907905e6ac5
-- title:
--   Eventual containment in a binary-weighted host forces all-base irrationality
-- statement:
--   Let H be a set of positive exponents with a finite-prime weighted summability witness at base two. Let A be infinite and suppose every element of A above some cutoff N belongs to H. Then, for every integer base b at least two, the reciprocal Mersenne subseries supported on A is irrational:
--
--   $$\sum_{a\in A}\frac{1}{b^a-1}\notin\mathbb{Q}. $$
--
--   Thus the weighted-host criterion remains useful when an infinite support has finitely many exceptional exponents outside the host.
-- source:
--   Downstream eventual-containment consequence of Will Cook’s #257 paper theorem and source finite-prefix lemma. Public main theorem: https://prove2.me/theorems/f6d332dc-466f-4f2a-a207-6b0455c0fbbd . Prefix-transfer source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/Erdos249257/CertificateKernel.lean#L9390-L9472 . Source paper (CC-BY-4.0; AI-assisted research disclosure): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex .

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Definitions.Def_Erdos249257_CertificateKernel
import Mathlib

theorem erdos257_eventual_weighted_host_irrationality
    (H A : Set ℕ) (N : ℕ)
    (hH0 : 0 ∉ H)
    (hWeighted : ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 H)
    (hAInf : A.Infinite)
    (hTailH : {n : ℕ | n ∈ A ∧ N < n} ⊆ H)
    (b : ℕ) (hb : 2 ≤ b) :
    Irrational (Erdos249257.erdosSupportSeries b A) := by sorry
