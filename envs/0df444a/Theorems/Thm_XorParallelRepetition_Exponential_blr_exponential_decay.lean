-- Prove2me | Theorems.Thm_XorParallelRepetition_Exponential_blr_exponential_decay
-- name    : XorParallelRepetition.Exponential.blr_exponential_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:47.790204+00:00
-- url     : https://prove2.me/theorems/703a8dbe-b01c-4d37-adb9-5001d7eb0141
-- title:
--   Claim 4.1 — exponential decay for the BLR game
-- statement:
--   Let $\Psi$ be a $k$-XOR game with $\operatorname{val}(\Psi)<1$, as fixed at the start of §4, and let $\Psi'$ be its BLR transform. Then there is $\varepsilon=\varepsilon(\Psi)>0$ such that
--
--   $$
--   \operatorname{val}\bigl((\Psi')^{\otimes n}\bigr)\le(1-\varepsilon)^n\qquad\text{for all }n\in\mathbb N.
--   $$
--
--   Together with Claim 4.2 this gives the main theorem.
--
--   Differences from the source:
--   - encoding: players [k] → an arbitrary finite type ι of players; reason: every finite type is in bijection with some Fin k, and the doubled players i, i′ become ι × Bool (or the remaining players × Bool); no instance changes
--   - generalization: a distribution µ on Σ₁ × … × Σ_k, with no finiteness stated, though the step dim(W) < ∞ on p. 9 needs finitely many questions → a probability mass function on arbitrary question types; reason: the source states no finiteness hypothesis, so none is added; every game with finite question sets is an instance, so the Lean statement specializes to the source's claim there
--   - encoding: val is the maximum acceptance probability → val is the supremum over all deterministic local strategies; reason: it equals the maximum whenever the maximum exists, and no attainment is assumed
--   - generalization: the remark after Theorem 1.3 speaks of k ⩾ 2 → every finite player set, including no player and one player; reason: ι = Fin k with k ⩾ 2 is a special case of the Lean statement
--   - encoding: Ψ′ has the target γ t(x) → Ψ′ is a generalized game whose law samples the target γ t(x) with the questions; reason: the verifier and its acceptance event are unchanged, and the target is not sent to the players
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Claim 4.1, printed p. 14, PDF p. 14; standing assumption of §4

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_BLR

namespace XorParallelRepetition.Exponential

universe u

/-- **Claim 4.1** (printed/PDF p. 14).  For a game `Ψ` as in Theorem 1.3, that is with
`val(Ψ) < 1`, the repeated values of its BLR transform decay exponentially. -/
theorem blr_exponential_decay {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : XorGame.{u} p ι) (hval : Ψ.val < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, Ψ.blr.repVal n ≤ (1 - ε) ^ n := by sorry

end XorParallelRepetition.Exponential
