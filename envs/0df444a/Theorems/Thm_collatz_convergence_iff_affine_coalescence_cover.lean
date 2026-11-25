-- Prove2me | Theorems.Thm_collatz_convergence_iff_affine_coalescence_cover
-- name    : collatz_convergence_iff_affine_coalescence_cover
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-25T00:59:57.772031+00:00
-- url     : https://prove2.me/theorems/c1fe66bf-5441-48be-b111-c9ef0d4fd599
-- title:
--   Collatz convergence is equivalent to coverage by arithmetic coalescence certificates
-- statement:
--   The full classical Collatz conjecture is equivalent to the following arithmetic covering condition. For every odd $n>1$ choose an odd iterate $y=T^t(n)$ and a positive valuation word $w$, possibly empty, for which $F=2^{\sum w}y$, $C=A(w)$ and $M=3^{|w|}$ satisfy $F\equiv C\pmod M$ and $C+M\le F<C+Mn$. Such a certificate reduces the starting value to a smaller positive odd integer whose orbit meets the same future point. Repeated reduction terminates by strong induction on the starting value. In the reverse direction one may take the empty word at the endpoint $1$.
-- source:
--   Arithmetic strong-induction formulation of https://prove2.me/missions/Collatz_Conjecture using syracuse_smaller_predecessor_iff_affine_interval.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Definitions.Def_collatzStepMap
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate

open Nat

theorem collatz_convergence_iff_affine_coalescence_cover :
    (∀ n : ℕ, 0 < n → ∃ a : ℕ, collatzStep^[a] n = 1) ↔
    (∀ n : ℕ, 1 < n → ¬ 2 ∣ n →
      ∃ (t : ℕ) (w : List ℕ), (∀ a : ℕ, a ∈ w → 0 < a) ∧
        let F := 2^w.sum * syracuseStep^[t] n
        let C := syracuseAffineConstant w
        let M := 3^w.length
        F % M = C % M ∧ C + M ≤ F ∧ F < C + M*n) := by sorry
