-- Prove2me | Theorems.Thm_ZamirInversion581_Mult_event_probability
-- name    : ZamirInversion581.Mult.event_probability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:13:06.272302+00:00
-- url     : https://prove2.me/theorems/60cc6acb-7a89-4145-806f-0dc7c36c1a20
-- title:
--   §2.1 event probability — $\Pr[E\mid B,C]=\beta_n\gamma_n^2\ge1/512$
-- statement:
--   Let $F$ be a finite field with $q$ elements, let $n\ge2$, and fix $B,C\in F^{n\times n}$. For independent uniform $R,A,A'\in F^{n\times n}$, let $E$ be the event that $R$, $I-R$, $A-BRC$, $A'-B(I-R)C$ are all invertible. Then, with $\beta_n=\Pr_R[R,I-R\in\mathrm{GL}_n(F)]$ and $\gamma_n=\prod_{i=1}^n(1-q^{-i})$,
--
--   $$
--   \Pr[E\mid B,C]=\beta_n\gamma_n^2\ge\frac1{512}.
--   $$
--
--   This holds for every fixed pair $B,C$, not only on average. For any fixed failure target, sufficiently many independent repetitions therefore reach the event $E$ with that probability on every input pair.
--
--   Differences from the source:
--   - generalization: the standing assumption n ≥ 3 in §2.1 (p.6) → n ≥ 2, as explicitly asserted in the sentence preceding the event-probability display (p.7); reason: this includes every instance under the section standing assumption and preserves the explicit n ≥ 2 claim; at n = 2 over F₂, β₂ = 1/8 and γ₂ = 3/8, so β₂γ₂² = 9/512 ≥ 1/512
-- source:
--   Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917, p.7, §2.1 event probability display; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/581.pdf

import Mathlib
import Definitions.Def_ZamirInversion581_Mult_Uniform
import Definitions.Def_ZamirInversion581_Mult_Inverter
import Definitions.Def_ZamirInversion581_Mult_SchurExecution

set_option autoImplicit false

namespace ZamirInversion581.Mult

/-- §2.1 event probability, p.7. Or Zamir, STOC 2027 submission #581 (October 2026), source.pdf
SHA-256 175df18b5c98634c390c15a304942f462478044bddc6b15bad02e5a2db2bb917. For `n ≥ 2` and every fixed `B, C`,
over independent uniform `R, A, A′`: `Pr[E | B, C] = β_n γ_n² ≥ 1/512`. -/
theorem event_probability (F : Type*) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (hn : 2 ≤ n)
    (B C : Matrix (Fin n) (Fin n) F) :
    unifProb (fun ω : Matrix (Fin n) (Fin n) F × Matrix (Fin n) (Fin n) F ×
        Matrix (Fin n) (Fin n) F => EventE B C ω.1 ω.2.1 ω.2.2) =
      betaN n F * gammaN n F ^ 2 ∧
    (1 : ℝ) / 512 ≤ betaN n F * gammaN n F ^ 2 := by sorry

end ZamirInversion581.Mult
