-- Prove2me | Theorems.Thm_ZKSheafPCP_Supplement_theorem_6_7
-- name    : ZKSheafPCP.Supplement.theorem_6_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T06:24:25.578527+00:00
-- url     : https://prove2.me/theorems/e162e696-658a-4ebb-bd12-e2c98c70fcf1
-- title:
--   Theorem 6.7 (corrected: bound quantifiers and empty-history index) — extendability implies local simulatability
-- statement:
--   Let $\mathbb F$ be a finite field, $P$ a finite coded space, $\mathcal F$ a sheaf of linear codes on $P$, $\sigma\in P$, $q\in\mathbb N$, and $S\subseteq P$ one cover such that, for every $c\in\mathcal F_\sigma$, $S$ is a $q$-extendable cover for the extension code $\mathcal F_{\sigma=c}$.
--
--   Then there exist actual message-query and clock bounds $l_S,t_S:\mathbb N\to\mathbb N$ such that
--
--   $$
--   l_S(k)\le (k+1)\max_{\tau\in S}|P_\tau\cap P_\sigma|
--   $$
--
--   and $t_S(k)$ is polynomially bounded in $(k+1)\max_{\tau\in S}|P_\tau|$, with explicit constant and exponent. Then $(\mathrm{ENC}_\sigma,S)$ is $(t_S,l_S,q)$-locally simulatable: one oracle Turing machine handles every history $Q\subseteq S$ with $|Q|<q$ that actually occurs in the encoding's support, halts within the stated clock on every seed, reads at most the stated number of message positions, and has exactly the conditional law of the uniform global extension encoding.
--
--   This theorem turns a combinatorial extendability property into an algorithmic exact-simulation guarantee.
--
--   Differences from the source:
--   - correction: arbitrary $l_S,t_S$ with $l_S(k)\le k\max_{\tau\in S}|P_\tau\cap P_\sigma|$ and only an upper-growth condition on $t_S$ → existence of actual bounds with $l_S(k)\le(k+1)\max_{\tau\in S}|P_\tau\cap P_\sigma|$ and $t_S(k)\in\operatorname{poly}((k+1)\max_{\tau\in S}|P_\tau|)$; reason: the printed quantifiers admit $l_S=t_S=0$, while an empty history still has one fresh query and the one-point full code must read and return its message symbol
--   - encoding: $t_S(k)\in\operatorname{poly}((k+1)\max_{\tau\in S}|P_\tau|)$ → explicit natural constants $C,e$ with $t_S(k)\le C((k+1)\max_{\tau\in S}|P_\tau|+2)^e$; reason: this is the quantified Lean meaning of a polynomial clock bound
--   - encoding: probabilistic oracle algorithm with exact conditional law → one oracle Turing machine run on a uniform field-valued seed, with its actual halting time and query log bounded and its decoded output PMF equal to the conditional encoding law; reason: this records the printed runtime, query and exact-law clauses operationally rather than by an unconstrained counter
--   - encoding: uniform distribution on $\mathcal F_{\sigma=c}(P)$ → `uniformOn` with the zero word as a default only if that set is empty; reason: the theorem's uniform extendability hypothesis makes the set nonempty for every allowed message, so the default changes no theorem instance
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Theorem 6.7, p.26

import Mathlib
import Definitions.Def_ZKSheafPCP_Supplement_IsLocallySimulatable
import Definitions.Def_ZKSheafPCP_simLaw

namespace ZKSheafPCP.Supplement

open Classical

/-- Theorem 6.7, p.26 (Zeilberger, O'Connor, Gur, Spooner,
*Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes*,
STOC 2027 submission, manuscript sha256 ac5e528f…): if one cover `S` is
`q`-extendable for every extension code `F_{σ=c}`, then the uniform extension
encoding `ENC_σ` has one local simulator with exact conditional law. There are
clock and message-query bounds for a history of `k < q` previous local queries
that are polynomial, respectively linear, in the data for the `k + 1` local
answers comprising that history and the fresh answer.

**Formalization Note** The page universally quantifies arbitrary `lS,tS` satisfying
only upper-growth inequalities. That admits `lS=tS=0`, although the one-point full
code requires the fresh query to read and return the message symbol. Lean states
the intended existence of actual bounds, and uses `k+1` because Definition 6.2's
history has `k` old queries plus one fresh query. `PolyBddIn` gives explicit
constant and exponent witnesses for the printed `poly`. -/
theorem theorem_6_7 {F D : Type} [Field F] [Fintype F] [Fintype D]
    (PP : CodedSpace D) (𝓕 : LocalCodes F D) (h𝓕 : 𝓕.IsSheaf PP)
    (σ : Finset D) (hσ : σ ∈ PP.P) (q : ℕ) (S : Finset (Finset D))
    (hS : ∀ c ∈ 𝓕.code σ,
      𝓕.IsRelKExtendableCover PP q (PP.geq σ) c S) :
    ∃ lS tS : ℕ → ℕ,
      (∀ k, lS k ≤ (k + 1) * S.sup (fun τ => (τ ∩ σ).card)) ∧
      PolyBddIn tS (fun k => (k + 1) * S.sup Finset.card) ∧
      IsLocallySimulatable (fun c : 𝓕.code σ => (c : D → F))
        (extensionEncoding PP 𝓕 σ) S tS lS q := by sorry

end ZKSheafPCP.Supplement
