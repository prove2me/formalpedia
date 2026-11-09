-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_lemma_2_2
-- name    : ZamirInversion581.Mult.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:35.928851+00:00
-- url     : https://prove2.me/theorems/26d5af01-ebad-4d08-9f75-384b94e7e71d
-- title:
--   Lemma 2.2 — the six ideal inversion calls fail together with $E$ with probability at most $6\cdot10^{-6}$
-- statement:
--   Let $F$ be a finite field, $n\ge3$, and let $I$ be an inversion oracle whose mean failure on uniform invertible matrices is at most $10^{-6}$ in dimensions $n$ and $2n$. Let $B,C,R,A,A'\in F^{n\times n}$ be independent and uniform. Then the probability that $E$ holds and at least one of the six ideal inversion calls, on $R$, $I-R$, $M$, $M'$, $S^{-1}$, $S'^{-1}$, is incorrect is at most
--
--   $$
--   6\cdot10^{-6}.
--   $$
--
--   Here $S,S',M,M'$ are as in the identity of §2.1. The bound is an average over $B,C$, and the paper does not claim it for a fixed pair. It shows that an inverter good on uniform invertible matrices rarely errs on the queries of the procedure.
--
--   Differences from the source:
--   - reading: "fails on at most a 10⁻⁶ fraction of uniformly random invertible matrices" → average success at least 1 − 10⁻⁶, i.e. mean failure probability at most 10⁻⁶ over GL_m; reason: for a randomized inverter the fraction is the probability over the input and the coins, as in Theorem 1.1
--   - encoding: probability over B, C, R, A, A′ and the coins of the six calls → uniform mean over (B, C, R, A, A′) of 𝟙_E(1 − ∏ᵢ(1 − φᵢ)); reason: given the ideal inputs the coins of the six calls are independent, so the conditional failure probability is exactly this expression
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.7, Lemma 2.2; p.8 "The inputs in the lemma are defined by the ideal execution"; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_ZamirInversion581_Mult_Inverter
import Definitions.Def_ZamirInversion581_Mult_SchurExecution

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-- Lemma 2.2, p.7. Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256
175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917. "Suppose the inverter fails on at
most a 10⁻⁶ fraction of uniformly random invertible matrices, in dimensions n and 2n. Then the
probability that E holds but one of the six inversion calls in our construction is incorrect is at
most 6 · 10⁻⁶." The probability is over independent uniform `B, C, R, A, A′` and the coins of the six
ideal calls (pp.7–8). -/
theorem lemma_2_2 (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (hn : 3 ≤ n)
    (I : InversionOracle F)
    (h₁ : 1 - (1 : ℝ) / 10 ^ 6 ≤ inverterSuccess I n)
    (h₂ : 1 - (1 : ℝ) / 10 ^ 6 ≤ inverterSuccess I (2 * n)) :
    unifMean (fun ω : Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F ×
        Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F =>
      idealFailureOnE I ω.1 ω.2.1 ω.2.2.1 ω.2.2.2.1 ω.2.2.2.2) ≤ 6 / 10 ^ 6 := by sorry

end ZamirInversion581.Mult
