-- Prove2me | Theorems.Thm_XorParallelRepetition_Exponential_repeated_value_le_blr
-- name    : XorParallelRepetition.Exponential.repeated_value_le_blr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:43.28346+00:00
-- url     : https://prove2.me/theorems/37c16224-750e-48c1-b743-cc8a3636c99b
-- title:
--   Claim 4.2 — repeated-game value domination
-- statement:
--   Let $\Psi$ be a $k$-XOR game and let $\Psi'$ be its BLR transform. For every $n\in\mathbb N$,
--
--   $$
--   \operatorname{val}(\Psi^{\otimes n})\le\operatorname{val}\bigl((\Psi')^{\otimes n}\bigr).
--   $$
--
--   Both sides are optimal values over all block strategies. The inequality transfers the decay of the BLR game to the original game.
--
--   Differences from the source:
--   - generalization: in §4, Ψ is fixed with val(Ψ) < 1 → every k-XOR game; reason: the displayed claim does not use the assumption; a game with val(Ψ) < 1 is a special case
--   - encoding: players [k] → an arbitrary finite type ι of players; reason: every finite type is in bijection with some Fin k, and the doubled players i, i′ become ι × Bool (or the remaining players × Bool); no instance changes
--   - generalization: a distribution µ on Σ₁ × … × Σ_k, with no finiteness stated, though the step dim(W) < ∞ on p. 9 needs finitely many questions → a probability mass function on arbitrary question types; reason: the source states no finiteness hypothesis, so none is added; every game with finite question sets is an instance, so the Lean statement specializes to the source's claim there
--   - encoding: val is the maximum acceptance probability → val is the supremum over all deterministic local strategies; reason: it equals the maximum whenever the maximum exists, and no attainment is assumed
--   - generalization: the remark after Theorem 1.3 speaks of k ⩾ 2 → every finite player set, including no player and one player; reason: ι = Fin k with k ⩾ 2 is a special case of the Lean statement
--   - encoding: Ψ′ has the target γ t(x) → Ψ′ is a generalized game whose law samples the target γ t(x) with the questions; reason: the verifier and its acceptance event are unchanged, and the target is not sent to the players
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Claim 4.2, printed p. 14, PDF p. 14

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_BLR

namespace XorParallelRepetition.Exponential

universe u

/-- **Claim 4.2** (printed/PDF p. 14).  `val(Ψ^{⊗n}) ≤ val((Ψ′)^{⊗n})`. -/
theorem repeated_value_le_blr {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ψ : XorGame.{u} p ι) (n : ℕ) :
    Ψ.repVal n ≤ Ψ.blr.repVal n := by sorry

end XorParallelRepetition.Exponential
