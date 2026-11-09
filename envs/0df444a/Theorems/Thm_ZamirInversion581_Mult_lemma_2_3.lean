-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_lemma_2_3
-- name    : ZamirInversion581.Mult.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:24.069276+00:00
-- url     : https://prove2.me/theorems/57f98c33-875a-404b-965f-68929e1e17c9
-- title:
--   Lemma 2.3 — $\Pr_R[R,I-R\in\mathrm{GL}_n(F_q)]\ge1/32$ for every finite field and $n\ge3$
-- statement:
--   For every finite field $F_q$ and every $n\ge3$, a uniformly random $R\in F_q^{n\times n}$ satisfies
--
--   $$
--   \Pr_R[R,\ I-R\in\mathrm{GL}_n(F_q)]\ge\frac1{32}.
--   $$
--
--   The constant is uniform in $q$, including $q=2$, where the two conditions are most in conflict. The bound shows that the complementary pair $(R,I-R)$ needed by the Schur complement procedure exists with constant probability over every finite field.
--
--   Differences from the source: none.
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.9, Lemma 2.3; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_ZamirInversion581_Mult_Inverter
import Definitions.Def_ZamirInversion581_Mult_SchurExecution

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-- Lemma 2.3, p.9. Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256
175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917. "For every finite field F_q and
every n ≥ 3, Pr_{R∼F_q^{n×n}}[R, I − R ∈ GL_n(F_q)] ≥ 1/32." -/
theorem lemma_2_3 (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (hn : 3 ≤ n) :
    (1 : ℝ) / 32 ≤ betaN n F := by sorry

end ZamirInversion581.Mult
