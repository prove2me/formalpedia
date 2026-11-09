-- Prove2me | Theorems.Thm_XorParallelRepetition_Exponential_finite_gluing_chain
-- name    : XorParallelRepetition.Exponential.finite_gluing_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:07:49.465321+00:00
-- url     : https://prove2.me/theorems/4648ed71-77a5-441d-817f-1aac59d8f85c
-- title:
--   Lemma 3.4 — finite gluing chain (corrected: zero-player constant-target obstruction excluded)
-- statement:
--   There is a function $B:\mathbb N\to\mathbb N$ with the following property. Let $\Psi$ be a generalized XOR game that has an ordered contradiction of length $N$, and suppose that $\Psi$ has at least one player, or that two supported challenges of $\Psi$ have different right hand sides. Then there are $T\le B(N)$ and a sequence of generalized XOR games $\Psi_0,\dots,\Psi_T$ such that
--
--   1. $\Psi_0=\Psi$;
--   2. for every $i<T$, $\Psi_{i+1}=(\Psi_i)_{\mathrm{glue}(I_i)}$ for some non-empty set $I_i$ of players of $\Psi_i$;
--   3. $\Psi_T$ has no players, and two supported challenges of $\Psi_T$ have different right hand sides.
--
--   The function $B$ depends on nothing but $N$: not on the game, its alphabets, its number of players, or $p$.
--
--   This chain is what Lemma 3.5 iterates Lemma 3.1 along.
--
--   Differences from the source:
--   - correction: every generalized game with an ordered contradiction of length N → the added hypothesis: at least one player, or two supported challenges with different right hand sides; reason: Definition 2.1 allows k = 0, and for p = 2 the point mass on t = 1 has the ordered contradiction of length 1 consisting of that challenge with sign +1, but no set of players can be glued, so T = 0 and the only right hand side is 1, against clause 3; the hypothesis excludes exactly the zero-player constant-target games
--   - reading: T = T(N) → T ≤ B(N) with B depending only on N, and T chosen with the chain; reason: a game with no players admits no gluing, so the exact length cannot be a function of N alone; the proof of the lemma bounds the number of steps in terms of N
--   - encoding: players [k] → an arbitrary finite type ι of players; reason: every finite type is in bijection with some Fin k, and the doubled players i, i′ become ι × Bool (or the remaining players × Bool); no instance changes
--   - generalization: a distribution µ on Σ₁ × … × Σ_k, with no finiteness stated, though the step dim(W) < ∞ on p. 9 needs finitely many questions → a probability mass function on arbitrary question types; reason: the source states no finiteness hypothesis, so none is added; every game with finite question sets is an instance, so the Lean statement specializes to the source's claim there
--   - encoding: a set I ⊆ [k] to glue over, with gluing defined for non-empty I → I : Finset ι together with I.Nonempty; reason: the non-emptiness of I is the domain of the operation in §3.1, not an extra assumption
--   - encoding: a sequence of games with changing player sets → a function from Fin (T + 1) to games packaged with their finite player type; reason: the terms have different types, so they are packaged; the games are unchanged
-- source:
--   Mark Braverman, Dor Minzer, STOC 2027 submission #195 (October 2026), Lemma 3.4, printed pp. 12–13, PDF pp. 12–13

import Mathlib
import Definitions.Def_XorParallelRepetition_Exponential_XorGames
import Definitions.Def_XorParallelRepetition_Exponential_Contradiction
import Definitions.Def_XorParallelRepetition_Exponential_Gluing

namespace XorParallelRepetition.Exponential

universe u

/-- **Lemma 3.4** (printed/PDF pp. 12–13), corrected for the zero-player constant-target
obstruction.  The length of the chain is bounded by a function of `N` alone. -/
theorem finite_gluing_chain :
    ∃ B : ℕ → ℕ, ∀ {p : ℕ} [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι]
      (Ψ : GeneralizedXorGame.{u} p ι) (N : ℕ),
      HasOrderedContradiction Ψ N → (Nonempty ι ∨ Ψ.HasTwoTargets) →
      ∃ (T : ℕ) (chain : Fin (T + 1) → PackedGame.{u} p),
        T ≤ B N ∧
        chain 0 = { Player := ι, game := Ψ } ∧
        (∀ i : Fin T, ∃ I : Finset (chain i.castSucc).Player,
          I.Nonempty ∧ chain i.succ = (chain i.castSucc).glue I) ∧
        IsEmpty (chain (Fin.last T)).Player ∧
        (chain (Fin.last T)).game.HasTwoTargets := by sorry

end XorParallelRepetition.Exponential
