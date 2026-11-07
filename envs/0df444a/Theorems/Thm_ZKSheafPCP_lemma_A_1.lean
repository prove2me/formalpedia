-- Prove2me | Theorems.Thm_ZKSheafPCP_lemma_A_1
-- name    : ZKSheafPCP.lemma_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:13:20.703195+00:00
-- url     : https://prove2.me/theorems/2a2ac8d2-95f3-4b3d-89cc-332f34c48a4c
-- title:
--   Lemma A.1 — Dinur's transformation preserves perfect zero knowledge
-- statement:
--   Let $(P,V)$ be a non-adaptive PZK-PCP system with constant-size alphabet, polynomial proof length $\ell(n)$, query complexity $q(n)$, query bound $b(n)$, polynomial decision complexity, perfect completeness and constant soundness error. Then there are constants $c_1,c_2>0$ and a PZK-PCP system $(P',V')$ with binary alphabet, proof length $\ell(n)\cdot q(n)^{c_1}$, query complexity $O(1)$, query bound $b(n)/q(n)^{c_2}$, perfect completeness and soundness error $1/2$.
--
--   This is the step from polylogarithmically many queries to a constant number.
--
--   **Formalization Note** The output has the same relation and no-set as the input.
--
--   Differences from the source:
--   - reading: "absolute constants c₁, c₂" → c₁, c₂, q₀ depending only on the alphabet bound A₀ and the soundness constant s; reason: the sketch's gap Ω(1/q) and repetition count depend on them; the goal uses one binary alphabet and s = 1/2, so its q₀ is still absolute
--   - reading: q(n)^{c₁}, b(n)/q(n)^{c₂} → max(q(n), 2)^{c₁} and the floor of b(n)/max(q(n), 2)^{c₂}; reason: b/q^{c₂} is undefined at q = 0, and at q = 1 the printed factor is 1, leaving no room even for the alphabet reduction
--   - reading: "polynomial decision complexity" → a machine with no oracle computes the verdict from x, the coins and the symbols read, in time polynomial in |x|; reason: the literal printed sense; no bound on V's number of coins is printed, and the sketch's constraint graph of size ℓ(n)·q(n)^{O(1)} is not implied by it, see MODERATION_NOTES
--   - encoding: "constnat-size alphabet" → A n ≤ A₀; reason: constant-size; the page has the typo
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Lemma A.1, p.46

import Mathlib
import Definitions.Def_ZKSheafPCP_PCPSys

open QAlgorithms.Complexity

namespace ZKSheafPCP

open Classical

/-- Lemma A.1, p.46 (Zeilberger, O'Connor, Gur, Spooner, *Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*, STOC 2027 submission (manuscript sha256 ac5e528f…)): a non-adaptive PZK-PCP system with constant-size alphabet, polynomial proof length `ℓ(n)`, query complexity `q(n)`, query bound `b(n)`, polynomial decision
complexity, perfect completeness and constant soundness error yields a PZK-PCP system with binary alphabet, proof length `ℓ(n) · q(n)^{c₁}`, query complexity `O(1)`, query bound `b(n)/q(n)^{c₂}`,
perfect completeness and soundness error `1/2`.

**Formalization Note** The constants depend only on the alphabet bound `A₀` and the soundness constant `s`; the sketch's gap `Ω(1/q)` and repetition count depend on them. `q(n)^{c}` is written with
`max(q(n), 2)`, since `b/q^{c₂}` is undefined at `q = 0`. The quotient is floored. The output has the same relation and no-set. -/
theorem lemma_A_1 (A₀ : ℕ) (s : ℝ) (hs : s < 1) :
    ∃ (c₁ c₂ q₀ : ℕ), 0 < c₁ ∧ 0 < c₂ ∧ ∀ (A ℓ q b B : ℕ → ℕ) (R : Set (Str × Str)) (No : Set Str)
      (Sys : PCPSys (fun x => x.length) A ℓ),
      (∀ n, A n ≤ A₀) → PolyBdd ℓ →
      Sys.Meets q (fun _ => s) b B R No → Sys.IsNonadaptive → Sys.DecisionPoly →
      ∃ ℓ' : ℕ → ℕ, (∀ n, ℓ' n ≤ ℓ n * (max (q n) 2) ^ c₁) ∧
        ∃ Sys' : PCPSys (fun x => x.length) (fun _ => 2) ℓ',
          Sys'.Meets (fun _ => q₀) (fun _ => 1 / 2) (fun n => b n / (max (q n) 2) ^ c₂) B R No := by sorry

end ZKSheafPCP
