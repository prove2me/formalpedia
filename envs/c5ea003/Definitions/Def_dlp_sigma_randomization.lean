-- Prove2me | Definitions.Def_dlp_sigma_randomization
-- name    : dlp_sigma_randomization
-- status  : Definition
-- author  : @Aphrodite
-- created : 2026-06-23T05:19:42.54314+00:00
-- url     : https://prove2.me/theorems/eb1e9968-ea5f-467d-aaac-4222c9d6f21a
-- statement:
--   σ-randomization scaffolding for the de la Peña–Montgomery-Smith decoupling construction (Ann. Probab. 23 (1995), 806–816; arXiv:math/9309211, §4, eq (4)). For each index the two i.i.d. copies $X^{(1)},X^{(2)}$ are reshuffled by an independent symmetric Bernoulli sign $\sigma\in\{\pm1\}$ into the decoupled pair $(Z^{(1)},Z^{(2)})=(X^{(1)},X^{(2)})$ if $\sigma=1$ and $(X^{(2)},X^{(1)})$ if $\sigma=-1$. `dlpCopyPerm σ` is the σ-permutation of $\{1,2\}$ with $Z^{(l)}=X^{(\mathrm{copyPerm}\,\sigma\,l)}$; `dlpCornerSign j l` is the eq (4) agreement sign ($+1$ if the copy superscript $j$ equals the target superscript $l$, else $-1$).
-- source:
--   de la Peña & Montgomery-Smith, Decoupling inequalities for the tail probabilities of multivariate U-statistics, Ann. Probab. 23 (1995), 806–816; arXiv:math/9309211, §4, eq (4).

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# de la Peña–Montgomery-Smith σ-randomization scaffolding

Core data structures for the sign-randomization construction of de la Peña and
Montgomery-Smith, "Decoupling inequalities for the tail probabilities of
multivariate U-statistics", Ann. Probab. 23 (1995), 806–816
(arXiv:math/9309211), Section 4, equation (4).

For each index the two i.i.d. copies `X^{(1)}, X^{(2)}` are reshuffled by an
independent symmetric Bernoulli sign `σ ∈ {±1}` into the decoupled pair
`(Z^{(1)}, Z^{(2)})`: `(Z^{(1)},Z^{(2)}) = (X^{(1)},X^{(2)})` if `σ = 1`, and
`(X^{(2)},X^{(1)})` if `σ = -1`.  In eq (4) the copy superscript appears with a
`+` sign when it agrees with the target superscript and a `-` sign otherwise.
These two notions are encoded by `copyPerm` (the σ-permutation of the two copies)
and `cornerSign` (the agreement sign).
-/

namespace MatrixCompletion

open scoped Classical BigOperators

/-- Eq (4) corner sign: `+1` if the copy superscript `j` agrees with the target
superscript `l`, `-1` otherwise. -/
noncomputable def dlpCornerSign (j l : Fin 2) : ℝ := if j = l then 1 else -1

/-- σ-permutation of the two i.i.d. copies (de la Peña–Montgomery-Smith §4):
`copyPerm σ = id` when `σ = 1`, the swap `Fin.rev` when `σ = -1`.  Reading off
`Z^{(l)} = X^{(copyPerm σ l)}`. -/
noncomputable def dlpCopyPerm (σ : ℝ) (l : Fin 2) : Fin 2 :=
  if σ = 1 then l else l.rev

end MatrixCompletion


