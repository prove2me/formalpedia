-- Prove2me | Theorems.Thm_BookSixth_bregman_minc_path_expansion
-- name    : BookSixth.bregman_minc_path_expansion
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T11:17:29.556012+00:00
-- url     : https://prove2.me/theorems/c768e144-b22a-45f7-8e19-12cfc6fccbfd
-- title:
--   Bregman-Minc: sequential assignment path expansion
-- statement:
--   Let $A$ be an $n$ by $n$ matrix of natural numbers and let $\pi$ order its rows. For a row $i$ and a set $U$ of unused columns, put $C_i(U)=\{j\in U:A_{ij}=1\}$. Let $F(L,U)$ be a real-valued function of a finite row list and an unused-column set satisfying
--
--   $$F([],U)=1,\qquad F(i::L,U)=\frac{1}{|C_i(U)|}\sum_{j\in C_i(U)}F(L,U\setminus\{j\}).$$
--
--   When $C_i(U)$ is empty, the second expression is defined to be zero. Let $L_\pi=(\pi(0),\ldots,\pi(n-1))$. Then
--
--   $$\sum_{\sigma\in\mathcal A(A)}qW(A,\sigma,\pi)=F(L_\pi,\{0,\ldots,n-1\}).$$
--
--   Here $\mathcal A(A)$ consists of permutations selecting an entry equal to one in each row, and $qW$ is the product of reciprocal available-choice counts. This identity connects compatible permutations with successful sequential assignment paths, separating the counting step from the elementary bound on finite averages. It includes $n=0$ and rows with no admissible entries; no positivity or zero-one hypothesis on the other entries is required.
-- source:
--   Source-derived intermediate lemma for BookSixth.bregman_minc_claimA, https://prove2.me/api/v1/theorems/89fed46f-e59d-4842-8051-e2b9e980c9cd, using the exact aSys/preS/avail/qW definitions in https://prove2.me/api/v1/theorems/52d231bb-cd49-4d96-840a-b424962608e2. The finite recursion and path expansion are an explicit formalization of the sequential-choice interpretation, not a separately numbered claim quoted from the paper. Parent source: J. Radhakrishnan, An entropy proof of Bregman's theorem (1997).

import Mathlib
import Definitions.Def_BregmanMincWeights
open scoped BigOperators
open BregmanMincWeights

theorem BookSixth.bregman_minc_path_expansion : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℕ) (π : Equiv.Perm (Fin n)) (F : List (Fin n) → Finset (Fin n) → ℝ), (∀ unused, F [] unused = 1) → (∀ i rows unused, F (i :: rows) unused = (∑ j ∈ unused.filter (fun j => A i j = 1), F rows (unused.erase j)) / ((unused.filter (fun j => A i j = 1)).card : ℝ)) → ∑ σ ∈ aSys A, qW A σ π = F ((List.finRange n).map π) Finset.univ := by sorry
