-- Prove2me | Theorems.Thm_ExtendedSmale9_sec_9_6_i_imp_ii
-- name    : ExtendedSmale9.sec_9_6_i_imp_ii
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T16:00:08.065065+00:00
-- url     : https://prove2.me/theorems/41df3480-d5ff-4748-9644-2053216340d2
-- title:
--   §9.6 (i) ⇒ (ii) — breakdown for a fixed $\hat\Lambda\in L^1(\Lambda)$ transfers to $\{\Xi,\Omega,M,\Lambda\}^{\Delta_1}$
-- statement:
--   Let $\{\Xi,\Omega,M,\Lambda\}$ be a computational problem and let $\hat\Lambda\in L^1(\Lambda)$. Then the strong breakdown epsilon of the problem with $\Delta_1$-information $\{\Xi,\Omega,M,\Lambda\}^{\Delta_1}$ is at least the strong breakdown epsilon of $\{\Xi,\Omega,M,\hat\Lambda\}$. In particular, statement (i) of §9.6 implies statement (ii).
-- source:
--   A. Bastounis, A. C. Hansen, V. Vlačić, *The extended Smale's 9th problem — On computational barriers and paradoxes in estimation, regularisation, computer-assisted proofs, and learning* (preprint, 126 pp., version of 28 Jan 2021), §9.6 'Different types of impossibility results', statements (i), (ii) and the remark 'Note that (i) ⇒ (ii)' (p. 28).

import Definitions.Def_ExtendedSmale9_GeneralAlgorithm
import Definitions.Def_ExtendedSmale9_Delta1
import Definitions.Def_ExtendedSmale9_LinearProgram
import Mathlib

open scoped ENNReal

namespace ExtendedSmale9

theorem sec_9_6_i_imp_ii {Ω Idx M : Type*} [MetricSpace M]
    (Λ : Idx → Ω → ℂ) (Ξ : Ω → Set M) (fhat : Idx → ℕ+ → Ω → ℂ)
    (hfhat : IsDelta1Info Λ fhat) :
    strongBreakdownEps (delta1Eval fhat) Ξ ≤
      strongBreakdownEps (delta1InputEval Λ) (fun q => Ξ q.input) := by sorry

end ExtendedSmale9
