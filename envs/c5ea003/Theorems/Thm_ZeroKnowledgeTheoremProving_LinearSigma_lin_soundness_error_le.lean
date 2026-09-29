-- Prove2me | Theorems.Thm_ZeroKnowledgeTheoremProving_LinearSigma_lin_soundness_error_le
-- name    : ZeroKnowledgeTheoremProving.LinearSigma.lin_soundness_error_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T02:10:22.676181+00:00
-- url     : https://prove2.me/theorems/b67fe543-a1cf-4130-80b1-6a25cacc8c02
-- title:
--   Soundness error `(1/q) ^ n`.
-- statement:
--   **Soundness error `(1/q) ^ n`.** For a statement with no witness the
--   fraction of answerable challenge vectors is at most `(1/q) ^ n`, an
--   exponentially stronger guarantee per round than the Boolean protocol whenever
--   `2 < q`.
--
--   ```lean
--   theorem ZeroKnowledgeTheoremProving.LinearSigma.lin_soundness_error_le(hno : ∀ w : V, ¬ LinIsWitness s w)
--       (P : LinParallelProver q V W n) :
--       ((linCheatSet s n P).card : ℚ) / (Finset.univ : Finset (Fin n → ZMod q)).card
--         ≤ (1 / q : ℚ) ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/ZeroKnowledgeTheoremProving/LargeChallengeSpace.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/ZeroKnowledgeTheoremProving/LargeChallengeSpace.lean#L167

-- Thm stub generated from Applications/ZeroKnowledgeTheoremProving/LargeChallengeSpace.lean
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_FiatShamir
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_LargeChallengeSpace

/-!
# Cycle 3: Linear Σ-Protocols over a Prime Field and `1 / q` Soundness

The Boolean protocol of the previous files has soundness error `1/2` per round.
This file generalises the whole development to a challenge space `ZMod q` with
`q` prime, i.e. to statements `f w = target` for a `ZMod q`-linear map
`f : V →ₗ[ZMod q] W`, and proves that everything survives with `1/2` replaced by
`1/q`:

* `linPerfectZeroKnowledge` — translating the tape by `c • w` is still a
  measure-preserving bijection, so the view is exactly the simulator's;
* `lin_special_soundness` — two accepting responses at *any two distinct*
  challenges extract the witness, now by dividing by `c - c'` in the field
  `ZMod q`. Subtraction is replaced by an honest linear solve;
* `linCheatSet_card_le_one` and `lin_soundness_error_le` — with no witness a
  committed prover answers at most one of the `q ^ n` challenge vectors, so the
  soundness error is `(1/q) ^ n`, exponentially better per round than the
  Boolean protocol;
* `linHonest_cheatSet_eq_univ` and `lin_amplified_dichotomy` — the honest prover
  answers all `q ^ n` challenge vectors, so the dichotomy from cycle 1 persists
  with an even larger gap;
* `challengeTerm_eq_smul` — the Boolean protocol is exactly the case `q = 2`,
  so the earlier results are the two-element specialisation of this family.

The cross-domain content is that soundness is now a statement of linear algebra
over a finite field (invertibility of a nonzero scalar) while privacy remains a
statement about a free translation action; the prime `q` interpolates between
them, and the soundness/privacy trade-off is governed by the field size.
-/

open ZeroKnowledgeTheoremProving.LinearSigma

open Finset

variable {q : ℕ} [Fact (Nat.Prime q)]
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod q) V] [Module (ZMod q) W]












/-! ### Amplification with challenge space of size `q` -/


variable (s : LinStatement q V W) (n : ℕ)







open scoped Classical in

theorem ZeroKnowledgeTheoremProving.LinearSigma.lin_soundness_error_le(hno : ∀ w : V, ¬ LinIsWitness s w)
    (P : LinParallelProver q V W n) :
    ((linCheatSet s n P).card : ℚ) / (Finset.univ : Finset (Fin n → ZMod q)).card
      ≤ (1 / q : ℚ) ^ n := by sorry
