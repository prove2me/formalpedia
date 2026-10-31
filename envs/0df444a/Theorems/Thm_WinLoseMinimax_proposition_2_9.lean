-- Prove2me | Theorems.Thm_WinLoseMinimax_proposition_2_9
-- name    : WinLoseMinimax.proposition_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:26:41.794029+00:00
-- url     : https://prove2.me/theorems/2a3e62d6-a666-4245-870b-b0e7d5c108e3
-- title:
--   Proposition 2.9, p.9 — finite rows: ascending-union closed ⇔ no ascending chain ⇔ LNG-free
-- statement:
--   Let $G=(S,T,\pi)$ be a game (of any cardinality) such that all sets in $\mathcal B^1(G)$ are finite, i.e. every row of the matrix of $G$ has finitely many 1's. Then the following are equivalent:
--
--   1. $\mathcal B^1_{\mathrm{down}}(G)$ is ascending-union closed;
--   2. $\mathcal B^1_{\mathrm{down}}(G)$ contains no countable ascending chain $A_1\subset A_2\subset\cdots\subset A_i\subset\cdots$;
--   3. $G$ is LNG-free.
--
--   This translates the condition of Theorem 2.2 into the forbidden-subgame language of Theorem 3.1 in the finite-row case, giving Corollary 2.10.
--
--   **Formalization Note** The chain in condition 2 is strict (`StrictMono`); a constant chain lies in every non-empty family, so the non-strict reading would make condition 2 always false. The equivalence is stated as `List.TFAE`.
--
--   Differences from the source:
--   - encoding: π : S × T → {0, 1}, payoff 1 = win of player 1 → `π : S → T → Bool`, `true` = 1; reason: same data
--   - reading: A₁ ⊂ A₂ ⊂ ⋯ in condition 2 (strictness not printed) → strictly increasing chain (`StrictMono`, indexed by ℕ); reason: under ⊆ a constant chain exists in every non-empty family and the proposition would fail, e.g. for the diagonal game of Remark 2.5
--   - encoding: A₁ ⊂ A₂ ⊂ ⋯ in Definition 2.1 (strictness not printed), i = 1, 2, … → `AscendingUnionClosed`: chains `A : ℕ → Set α` with `StrictMono A`; reason: a non-strict chain is eventually constant, so its union is a member, or has a strictly increasing subsequence with the same union; the two readings define the same families
--   - encoding: LNG on the positive integers 1, 2, … → `lng` on ℕ = {0, 1, …} with `lng s t = true ↔ t ≤ s`; reason: the shift k ↦ k − 1 is an isomorphism of games
--   - reading: "isomorphic to the larger number game" (no definition printed) → `GameIso`: bijections of the strategy sets, players keeping their roles, preserving the payoff; reason: standard isomorphism of normal-form games; matches the p.9 description (a lower-triangular submatrix with rows from S)
-- source:
--   Holzman, The minimax property in infinite two-person win-lose games, arXiv:2310.19314v1, Proposition 2.9, p.9

import Mathlib
import Definitions.Def_WinLoseMinimax_Game
import Definitions.Def_WinLoseMinimax_Families

open scoped ENNReal

namespace WinLoseMinimax

universe u v

/-- **Proposition 2.9.** Holzman, arXiv:2310.19314v1, Proposition 2.9, p.9: let `G = (S, T, π)`
be a game such that all sets in the family `B¹(G)` are finite. Then the following three
conditions are equivalent:
1. `B¹_down(G)` is ascending-union closed.
2. `B¹_down(G)` contains no countable ascending chain `A₁ ⊂ A₂ ⊂ ⋯ ⊂ Aᵢ ⊂ ⋯`.
3. `G` is LNG-free.

**Formalization Note.** Any game: `S`, `T` arbitrary non-empty types, no countability. "All sets
in `B¹(G)` are finite" is `∀ s, (rowSet π s).Finite`. In condition 2 the chain is strict
(`StrictMono`, indexed by `ℕ`): a constant chain lies in every non-empty family, so the
non-strict reading would make condition 2 always false. -/
theorem proposition_2_9 {S : Type u} {T : Type v} [Nonempty S] [Nonempty T]
    (π : S → T → Bool) (hfin : ∀ s, (rowSet π s).Finite) :
    List.TFAE
      [AscendingUnionClosed (B1down π),
       ¬ ∃ A : ℕ → Set T, (∀ i, A i ∈ B1down π) ∧ StrictMono A,
       LNGFree π] := by sorry

end WinLoseMinimax
