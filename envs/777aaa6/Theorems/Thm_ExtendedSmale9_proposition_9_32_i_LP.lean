-- Prove2me | Theorems.Thm_ExtendedSmale9_proposition_9_32_i_LP
-- name    : ExtendedSmale9.proposition_9_32_i_LP
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T16:07:55.469344+00:00
-- url     : https://prove2.me/theorems/968261a3-954e-4512-97e8-ec3560ca42df
-- title:
--   Proposition 9.32 (i) for LP, deterministic consequence — $\varepsilon_B^s>10^{-K}$
-- statement:
--   Let $K\ge1$ be an integer, $4\le m<N$, and $p\in[1,\infty]$, and let $\Xi$ be the LP solution map (1.1) with $c=\mathbf 1_N$, taking values in $M_N=(\mathbb R^N,\|\cdot\|_p)$.
--
--   There exist a nonempty set $\Omega_{m,N}$ of inputs $(y,A)\in\mathbb R^m\times\mathbb R^{m\times N}$ and a family $\hat\Lambda_{m,N}\in L^1(\Lambda_{m,N})$ of $\Delta_1$-information for the entries of $(y,A)$ with the following properties. Every input in $\Omega_{m,N}$ has a nonempty solution set, $\|y\|_\infty\le2$ and $\|A\|_{\max}=1$. The problem $\{\Xi,\Omega_{m,N},M_N,\hat\Lambda_{m,N}\}$ satisfies $\varepsilon_B^s>10^{-K}$.
--
--   This is the deterministic consequence $\varepsilon_B^s\ge\varepsilon_{PB}^s(p)\ge\varepsilon_{PhB}^s(p)>10^{-K}$ of Proposition 9.32 (i), obtained via Proposition 10.1. The condition-number bounds of Proposition 9.32 are not included.
-- source:
--   A. Bastounis, A. C. Hansen, V. Vlačić, *The extended Smale's 9th problem — On computational barriers and paradoxes in estimation, regularisation, computer-assisted proofs, and learning* (preprint, 126 pp., version of 28 Jan 2021), §9.7, Proposition 9.32 (i) with (9.13)–(9.14) (p. 29), combined with Proposition 10.1, (10.1) and (10.3) (p. 36).

import Definitions.Def_ExtendedSmale9_GeneralAlgorithm
import Definitions.Def_ExtendedSmale9_Delta1
import Definitions.Def_ExtendedSmale9_LinearProgram
import Mathlib

open scoped ENNReal

namespace ExtendedSmale9

theorem proposition_9_32_i_LP (K : ℕ) (hK : 1 ≤ K) (m N : ℕ) (hm : 4 ≤ m) (hmN : m < N)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ Ω : Set (LPInput m N), Ω.Nonempty ∧
      (∀ ι ∈ Ω, (lpArgmin (fun _ => 1) ι.1 ι.2).Nonempty ∧ (∀ i, |ι.1 i| ≤ 2) ∧
        (∀ i j, |ι.2 i j| ≤ 1) ∧ ∃ i j, |ι.2 i j| = 1) ∧
      ∃ fhat : (Fin m ⊕ (Fin m × Fin N)) → ℕ+ → Ω → ℂ,
        IsDelta1Info (fun k (ι : Ω) => lpEval k ι.1) fhat ∧
        ENNReal.ofReal (10 ^ (-(K : ℤ))) <
          strongBreakdownEps (delta1Eval fhat) (fun ι : Ω => lpSolution p ι.1) := by sorry

end ExtendedSmale9
