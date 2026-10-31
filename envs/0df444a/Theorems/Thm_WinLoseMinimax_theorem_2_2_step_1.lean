-- Prove2me | Theorems.Thm_WinLoseMinimax_theorem_2_2_step_1
-- name    : WinLoseMinimax.theorem_2_2_step_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:25:37.34914+00:00
-- url     : https://prove2.me/theorems/23d73dbe-daac-4b65-976b-197e62793b41
-- title:
--   Proof of Theorem 2.2, Step 1, p.6 — $B^1_{down}(G)$ is a closed subset of $\{0,1\}^{\mathbb N}$
-- statement:
--   Let $G=(S,T,\pi)$ be a countable game ($S$ and $T$ countably infinite) such that $\mathcal B^1_{\mathrm{down}}(G)$ is ascending-union closed. Identify each subset $A\subseteq T$ with its characteristic function in $\{0,1\}^T$, where $\{0,1\}$ carries the discrete topology and $\{0,1\}^T$ the product topology. Then
--
--   $$\mathcal B^1_{\mathrm{down}}(G)\ \text{is a closed subset of}\ \{0,1\}^T,$$
--
--   hence is itself a compact metric space.
--
--   This compactness is what lets the proof of Theorem 2.2 take weak limits of optimal strategies.
--
--   **Formalization Note** $\{0,1\}^T$ is `T → Bool` with the product topology; the paper identifies $T$ with the positive integers, which changes this space only by a homeomorphism. The conclusion has three parts: the set is closed, it is compact, and as a subspace it is metrizable.
--
--   Differences from the source:
--   - encoding: countable game, |S| = |T| = ℵ₀ (Definition 1.1) → `[Countable S] [Infinite S] [Countable T] [Infinite T]`; reason: exactly countably infinite S and T
--   - encoding: {0,1}^ℕ after identifying T with ℕ → `T → Bool` with the product topology, a function z ↔ the set {t | z t = true}; reason: the identification is a homeomorphism; closedness, compactness and metrizability are preserved
--   - encoding: "hence is itself a compact metric space" → `IsCompact` of the set and `MetrizableSpace` of the subspace; reason: a compact metric space is a compact metrizable space
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - encoding: A₁ ⊂ A₂ ⊂ ⋯ in Definition 2.1 (strictness not printed), i = 1, 2, … → `AscendingUnionClosed`: chains `A : ℕ → Set α` with `StrictMono A`; reason: a non-strict chain is eventually constant, so its union is a member, or has a strictly increasing subsequence with the same union; the two readings define the same families
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, proof of Theorem 2.2, Step 1, p.6

import Mathlib
import Definitions.Def_WinLoseMinimax_Game
import Definitions.Def_WinLoseMinimax_Families

open scoped ENNReal

namespace WinLoseMinimax

universe u v

/-- **Proof of Theorem 2.2, Step 1: `B¹_down(G)` is closed.** Holzman, arXiv:2310.19314v1, proof
of Theorem 2.2, Step 1, p.6: let `G = (S, T, π)` be a countable game such that `B¹_down(G)` is
ascending-union closed. Viewing each subset of `T` as its characteristic function in `{0, 1}^T`
(`{0,1}` discrete, product topology), `B¹_down(G)` is a closed subset of `{0, 1}^T`, hence is
itself a compact metric space.

**Formalization Note.** "Countable game" (Definition 1.1, `|S| = |T| = ℵ₀`) is
`[Countable S] [Infinite S] [Countable T] [Infinite T]`. `{0, 1}^T` is `T → Bool` with the
product (`Pi`) topology of the discrete `Bool`; the paper identifies `T` with `ℕ`, which does not
change this space up to homeomorphism. A function `z` corresponds to the set `{t | z t = true}`.
"Compact metric space" is `IsCompact` of the set plus metrizability of the subspace. -/
theorem theorem_2_2_step_1 {S : Type u} {T : Type v} [Countable S] [Infinite S]
    [Countable T] [Infinite T] (π : S → T → Bool)
    (hAUC : AscendingUnionClosed (B1down π)) :
    IsClosed {z : T → Bool | {t | z t = true} ∈ B1down π} ∧
      IsCompact {z : T → Bool | {t | z t = true} ∈ B1down π} ∧
      TopologicalSpace.MetrizableSpace {z : T → Bool // {t | z t = true} ∈ B1down π} := by sorry

end WinLoseMinimax
