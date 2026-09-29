-- Prove2me | Definitions.Def_Novelty_SYZDualityRankN
-- name    : Novelty_SYZDualityRankN
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:40:55.900414+00:00
-- url     : https://prove2.me/theorems/fed6c76b-b55d-4081-8530-b81d53da14dd
-- title:
--   Aether Catalog definitions — Novelty_SYZDualityRankN
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SYZDualityRankN`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SYZDualityRankN.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_SYZMonodromyDuality

/-!
# Arithmetic Mirror Symmetry VII — T-duality is inner only in rank one

This file closes **Conjecture C** of the previous cycle's `FUTURE_DIRECTIONS.md`, and
sharpens it.  Cycle 1 proved that fiberwise SYZ T-duality `M ↦ (M⁻¹)ᵀ` is an involutive
automorphism of the integral monodromy group `GL_n(ℤ)`, that it is realized by conjugation
with the symplectic matrix on `SL₂(ℤ)` (`Novelty.MirrorBridge.sl2_dual_conj`), and that it
is **not** inner in rank three (`dualMon_not_inner_rank_three`).  Conjecture C asked for the
uniform statement in every rank `n ≥ 3`.

The uniform statement is proved here, and the answer turns out to be sharper than
conjectured: on the *full* monodromy group `GL_n(ℤ)` dualization is not inner for **every**
`n ≥ 2`.  The rank-two positive result is therefore genuinely a statement about `SL₂(ℤ)`:
the determinant hypothesis in `sl2_dual_conj` cannot be dropped, because for `det M = −1`
one gets `(M⁻¹)ᵀ = −J M J⁻¹`.  Only in rank one is dualization inner, and there it is the
identity.

## Main results

* `dualMon_not_inner_of_trace_ne` — the general obstruction: a single monodromy matrix with
  `tr M⁻¹ ≠ tr M` shows dualization is not inner, because conjugation and transposition both
  preserve the trace.
* `embedBlock`, `embedBlock_mul`, `embedBlock_trace`, `embedBlock_det` — stabilization of a
  monodromy matrix by an identity block, transported to `Fin (r + k)` by `reindex`.
* `dualMon_not_inner_rank_ge_three` — **Conjecture C**: for every `n ≥ 3` dualization is not
  an inner automorphism of `GL_n(ℤ)`, witnessed by a matrix of determinant `1` (so it is not
  inner on `SL_n(ℤ)` either).
* `dualMon_not_inner_rank_ge_two` — the sharpening: for every `n ≥ 2` dualization is not
  inner on `GL_n(ℤ)`, witnessed by the hyperbolic matrix `[[2,1],[1,0]]` of determinant `−1`.
* `sl2_dual_conj_fails_for_det_neg_one` — the determinant hypothesis of `sl2_dual_conj` is
  necessary: for `det M = −1` one has `(M⁻¹)ᵀ = −(J M J⁻¹)`, and the two differ.
* `dualMon_rank_one` / `dualMon_inner_rank_one` — in rank one dualization is the identity.
* `dualMon_inner_iff_rank_le_one` — the resulting **dichotomy**: dualization is an inner
  automorphism of `GL_n(ℤ)` if and only if `n ≤ 1`.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  Cycle 1 suggested "inner exactly for `n ≤ 2`".  The
  trace obstruction `tr M ≠ tr M⁻¹`, which killed rank three, should stabilize: padding a
  witness by an identity block adds the same constant `k` to both traces, so the difference
  is preserved in every larger rank.
* **Experiment (Experimenter).**  Implemented padding as
  `reindex finSumFinEquiv finSumFinEquiv (fromBlocks A 0 0 1)`; multiplicativity comes from
  `Matrix.reindexAlgEquiv` and `Matrix.fromBlocks_multiply`, the trace from
  `Fintype.sum_sum_type`, and the determinant from `Matrix.det_fromBlocks_zero₁₂`.  Running
  the padding on the rank-three companion matrix of `x³ − 2x² + x − 1` gives traces
  `2 + k` and `1 + k`, closing every rank `n ≥ 3` at once.
* **Analysis (Analyst).**  Testing the same obstruction in rank two produced a surprise:
  `[[2,1],[1,0]]` has `tr = 2` and `tr⁻¹ = −2`, so dualization is not inner on `GL₂(ℤ)`
  either.  The rank-two positive result is thus *not* a rank phenomenon but a
  **determinant** phenomenon — the symplectic conjugation computes `(M⁻¹)ᵀ` only up to the
  factor `det M`.  Conjecture C was therefore true but stated one rank too weakly.
* **Critique (Critic).**  Every statement below is a genuine inequality of integers or an
  explicit matrix identity; no `decide`, no `native_decide`.  The rank-one positive result
  is not vacuous: it produces the explicit conjugator `1` and uses the fact that the only
  units of `ℤ` are `±1`.  The dichotomy `dualMon_inner_iff_rank_le_one` covers `n = 0`
  as well (the trivial group).
* **Synthesis (PI).**  On the full integral monodromy group, T-duality is an outer
  automorphism in every rank `≥ 2`; a rank-`n` integral SYZ local system with full monodromy
  is therefore isomorphic to its T-dual only in rank `≤ 1`, and the rank-two "self-duality"
  of elliptic fibrations is exactly the orientation-preserving (`SL₂`) part of the story.
-/

namespace Novelty.MirrorBridge

open Matrix

section Obstruction

variable {n : ℕ}



end Obstruction

section Stabilization

/-! ### Padding a monodromy matrix by an identity block

A rank-`r` witness is turned into a rank-`(r + k)` witness by acting trivially on `k`
further lattice directions.  Both the trace and the determinant behave transparently. -/

variable {r k : ℕ}

/-- Stabilize an `r × r` monodromy matrix to size `r + k` by an identity block. -/
def embedBlock (r k : ℕ) (A : Matrix (Fin r) (Fin r) ℤ) : Matrix (Fin (r + k)) (Fin (r + k)) ℤ :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 1)






end Stabilization

section RankGeThree

/-- The rank-`n` stabilization (`n = 3 + k`) of the companion matrix of `x³ − 2x² + x − 1`. -/
def gl3Stab (k : ℕ) : Matrix (Fin (3 + k)) (Fin (3 + k)) ℤ := embedBlock 3 k gl3Example

/-- Its inverse. -/
def gl3StabInv (k : ℕ) : Matrix (Fin (3 + k)) (Fin (3 + k)) ℤ := embedBlock 3 k gl3ExampleInv







end RankGeThree

section RankGeTwo

/-! ### Rank two: dualization is inner on `SL₂(ℤ)` but not on `GL₂(ℤ)`

The symplectic conjugation of `sl2_dual_conj` computes the adjugate transpose, which equals
`(M⁻¹)ᵀ` only after dividing by `det M`.  For `det M = −1` the two differ by a sign, and the
trace obstruction detects this. -/

/-- The hyperbolic monodromy `[[2,1],[1,0]]`, of determinant `−1`. -/
def gl2Hyper : Matrix (Fin 2) (Fin 2) ℤ := !![2, 1; 1, 0]

/-- Its inverse `[[0,1],[1,−2]]`. -/
def gl2HyperInv : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -2]






/-- The stabilized rank-`(2+k)` hyperbolic witness. -/
def gl2Stab (k : ℕ) : Matrix (Fin (2 + k)) (Fin (2 + k)) ℤ := embedBlock 2 k gl2Hyper

/-- Its inverse. -/
def gl2StabInv (k : ℕ) : Matrix (Fin (2 + k)) (Fin (2 + k)) ℤ := embedBlock 2 k gl2HyperInv





end RankGeTwo

section RankOne




end RankOne


end Novelty.MirrorBridge


