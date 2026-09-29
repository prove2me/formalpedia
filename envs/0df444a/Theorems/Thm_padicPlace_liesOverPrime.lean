-- Prove2me | Theorems.Thm_padicPlace_liesOverPrime
-- name    : padicPlace_liesOverPrime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/2f070313-b5e3-571e-b510-7fd4eaa0b678
-- title:
--   The chosen place of ℚ̄ above p lies over p
-- statement:
--   Let $p$ be a prime. Consider the $\mathbb Q$-algebra embedding [`padicEmbedding p`](def/GaloisRep_CompletionBridge.html#L17) of $\overline{\mathbb Q}$ (the Lean `AlgebraicClosure ℚ`) into `PadicAlgCl p`, obtained by lifting along algebraic closedness, and the valuation subring [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) of `PadicAlgCl p` cut out by its $\mathbb R_{\ge 0}$-valued valuation; [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) is the valuation subring of $\overline{\mathbb Q}$ obtained by pulling [`padicIntegers p`](def/GaloisRep_CompletionBridge.html#L20) back along this embedding. The theorem asserts that [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) satisfies the predicate `LiesOverPrime p`, which by definition says that the image of the natural number $p$ in $\overline{\mathbb Q}$ belongs to the nonunits of [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25), i.e. that $p$ lies in the maximal ideal of this valuation ring; equivalently, the valuation of $p$ attached to [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25) is strictly less than $1$, so the chosen place of $\overline{\mathbb Q}$ determined by the embedding into $\overline{\mathbb Q}_p$ is a place above $p$ and not above any other rational prime.
--
--   This records the basic normalisation property of the fixed $p$-adic place of $\overline{\mathbb Q}$ used throughout the local analysis of Galois representations, in the form of the project's predicate `LiesOverPrime`. It is invoked whenever an argument must pass between an arbitrary place of $\overline{\mathbb Q}$ above $p$ and the distinguished one coming from the embedding into $\overline{\mathbb Q}_p$, for instance in the treatment of ordinarity and of ramification conditions at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_padicPlace_liesOverPrime.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem padicPlace_liesOverPrime (p : ℕ) [Fact p.Prime] :
    (padicPlace p).LiesOverPrime p := by sorry
