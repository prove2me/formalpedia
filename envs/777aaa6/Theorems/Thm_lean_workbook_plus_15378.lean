-- Prove2me | Theorems.Thm_lean_workbook_plus_15378
-- name    : lean_workbook_plus_15378
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/11e6fe7c-0840-4099-ace9-1f1fd868017e
-- statement:
--   First, note that, the set of primes $\mathcal{P}=\{p:\exists n \in\mathbb{Z}^+,p\mid 3n^2+1\}$ is infinite (well known, via the fact that $-3$ is a quadratic residue, modulo prime $p\equiv 1\pmod{6}$). Now, for any such $p\in \mathcal{P}$, note, $p\mid 3(p-n)^2+1$ and $p\mid 3n^2+1$. Let $k=\min\{n,p-n\}$. Note that, $p>2k$, and $p\mid 3k^2+1$, as desired.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15378 : Set.Infinite {p : ℕ | ∃ n : ℕ, p ∣ 3 * n ^ 2 + 1}   :=  by sorry
