-- Prove2me | Theorems.Thm_ExtendedSmale9_theorem_3_4_i_LP
-- name    : ExtendedSmale9.theorem_3_4_i_LP
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T16:22:49.181999+00:00
-- url     : https://prove2.me/theorems/6b1b6901-4d96-440d-9bd3-5c78d39b5dc5
-- title:
--   Theorem 3.4 (i), deterministic part, LP — no algorithm computes $K$ correct digits
-- statement:
--   Let $K\ge1$ be an integer, $4\le m<N$ and $p\in[1,\infty]$, and let $\Xi$ be the LP solution map (1.1) with $c=\mathbf 1_N$, with errors measured in $\|\cdot\|_p$.
--
--   There is a nonempty class $\Omega_{m,N}$ of inputs $(y,A)\in\mathbb R^m\times\mathbb R^{m\times N}$ with the following properties. Every input has a nonempty solution set, $\|y\|_\infty\le2$ and $\|A\|_{\max}=1$. **No** general algorithm that reads dyadic oracle approximations of the entries of $(y,A)$ (the extended model with $\Delta_1$-information) produces $K$ correct digits, i.e.
--   $$\operatorname{dist}_{\ell^p}(\Gamma(\tilde\iota),\Xi(\iota))\le10^{-K}$$
--   for every oracle representation $\tilde\iota$ of every $\iota\in\Omega_{m,N}$.
--
--   This is the deterministic statement in Theorem 3.4 (i), in the fixed-dimension form allowed by Theorem 3.4 (v). The randomised statements and the condition-number bounds are not included.
-- source:
--   A. Bastounis, A. C. Hansen, V. Vlačić, *The extended Smale's 9th problem — On computational barriers and paradoxes in estimation, regularisation, computer-assisted proofs, and learning* (preprint, 126 pp., version of 28 Jan 2021), §3.2, Theorem 3.4 (i) together with (v) (fixed dimensions $m\ge4$, $N>m$; $K$ may be $1$) and the well-conditioning remark (bounds on $\|y\|_\infty$, $\|A\|_{\max}$), with (3.1)–(3.2) (pp. 7–8).

import Definitions.Def_ExtendedSmale9_GeneralAlgorithm
import Definitions.Def_ExtendedSmale9_Delta1
import Definitions.Def_ExtendedSmale9_LinearProgram
import Mathlib

open scoped ENNReal

namespace ExtendedSmale9

theorem theorem_3_4_i_LP (K : ℕ) (hK : 1 ≤ K) (m N : ℕ) (hm : 4 ≤ m) (hmN : m < N)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ Ω : Set (LPInput m N), Ω.Nonempty ∧
      (∀ ι ∈ Ω, (lpArgmin (fun _ => 1) ι.1 ι.2).Nonempty ∧ (∀ i, |ι.1 i| ≤ 2) ∧
        (∀ i j, |ι.2 i j| ≤ 1) ∧ ∃ i j, |ι.2 i j| = 1) ∧
      ¬ ∃ Γ : GeneralAlgorithm (delta1InputEval (fun k (ι : Ω) => lpEval k ι.1))
          (PiLp p (fun _ : Fin N => ℝ)),
        ∀ q, errDist (Γ.run q) (lpSolution p q.input.1) ≤ ENNReal.ofReal (10 ^ (-(K : ℤ))) := by sorry

end ExtendedSmale9
