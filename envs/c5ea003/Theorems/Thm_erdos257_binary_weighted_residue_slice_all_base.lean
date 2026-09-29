-- Prove2me | Theorems.Thm_erdos257_binary_weighted_residue_slice_all_base
-- name    : erdos257_binary_weighted_residue_slice_all_base
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T13:37:07.411594+00:00
-- url     : https://prove2.me/theorems/f1062fc5-c8c2-4c16-b0ad-da94188dd9f8
-- title:
--   Infinite residue slices of binary-weighted hosts are irrational at every base
-- statement:
--   Let $H$ be an infinite set of positive integers. For a nonempty finite set $P$ of primes, write $p_P(n)=\prod_{p\in P}p^{v_p(n)}$ for the part of $n$ supported on $P$. Assume that, for some such $P$, the binary weighted series is finite:
--
--   $$
--   \sum_{n\in H}\frac{p_P(n)}{n(2^{p_P(n)}-1)}<\infty.
--   $$
--
--   Choose natural numbers $m,r$ and put $A=\{n\in H:n\bmod m=r\}$. If $A$ is infinite, then for every integer base $b\ge2$,
--
--   $$
--   \sum_{n\in A}\frac{1}{b^n-1}\notin\mathbb Q.
--   $$
--
--   This makes the all-base hereditary conclusion of the proved weighted-support theorem available for an explicitly infinite congruence slice of one fixed binary-weighted host.
--
--   **Formalization Note** The infinitude premise is required for the selected slice; it does not assert that every residue slice is infinite. Lean's totalized natural-number remainder makes the $m=0$ case vacuous under that premise.
-- source:
--   Public full paper-Theorem-1 wrapper: https://prove2.me/theorems/f6d332dc-466f-4f2a-a207-6b0455c0fbbd . The wrapper composes two accepted Lean declarations; source paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L54-L75 . The paper discloses substantial AI-assisted research and drafting: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188 . The residue-slice consequence and proof were proposed in an isolated public-only reader trial; owner-side formatting followed without changing the argument.

import Definitions.Def_ErdosProblems_Erdos257_PaperCompleteR7_AnalyticTargets
import Mathlib

theorem erdos257_binary_weighted_residue_slice_all_base
    (H : Set ℕ) (m r : ℕ) (hzero : 0 ∉ H) (hinf : H.Infinite)
    (hweighted : ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 H)
    (hclass : (H ∩ {n : ℕ | n % m = r}).Infinite) :
    ∀ b : ℕ, 2 ≤ b →
      Irrational (Erdos249257.erdosSupportSeries b
        (H ∩ {n : ℕ | n % m = r})) := by sorry
