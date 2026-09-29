-- Prove2me | Definitions.Def_Applications_ZeroKnowledgeTheoremProving_LargeChallengeSpace
-- name    : Applications_ZeroKnowledgeTheoremProving_LargeChallengeSpace
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T01:02:32.43264+00:00
-- url     : https://prove2.me/theorems/5c521c7c-4024-4de1-b067-795e23a21404
-- title:
--   Aether Catalog definitions — Applications_ZeroKnowledgeTheoremProving_LargeChallengeSpace
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.ZeroKnowledgeTheoremProving.LargeChallengeSpace`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/ZeroKnowledgeTheoremProving/LargeChallengeSpace.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_ZeroKnowledgeTheoremProving_FiatShamir

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

namespace ZeroKnowledgeTheoremProving.LinearSigma

open Finset

variable {q : ℕ} [Fact (Nat.Prime q)]
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
  [Module (ZMod q) V] [Module (ZMod q) W]

/-- A public linear statement: prove knowledge of `w` with `f w = target`. -/
structure LinStatement (q : ℕ) [Fact (Nat.Prime q)] (V W : Type*)
    [AddCommGroup V] [AddCommGroup W] [Module (ZMod q) V] [Module (ZMod q) W] where
  hom : V →ₗ[ZMod q] W
  target : W

/-- A witness is a preimage of the public target. -/
def LinIsWitness (s : LinStatement q V W) (w : V) : Prop := s.hom w = s.target

/-- The public transcript, with challenge drawn from the field `ZMod q`. -/
structure LinTranscript (q : ℕ) (V W : Type*) where
  commitment : W
  challenge : ZMod q
  response : V

/-- Honest transcript from witness `w`, tape `r` and challenge `c`. -/
def linReal (s : LinStatement q V W) (w r : V) (c : ZMod q) : LinTranscript q V W :=
  ⟨s.hom r, c, r + c • w⟩

/-- Simulated transcript from a freely chosen response. -/
def linSim (s : LinStatement q V W) (z : V) (c : ZMod q) : LinTranscript q V W :=
  ⟨s.hom z - c • s.target, c, z⟩

/-- The verifier's linear equation. -/
def LinAccepts (s : LinStatement q V W) (t : LinTranscript q V W) : Prop :=
  s.hom t.response = t.commitment + t.challenge • s.target


/-- Translation of the tape by `c • w` is a bijection of the tape space. -/
def linTapeEquiv (c : ZMod q) (w : V) : V ≃ V where
  toFun r := r + c • w
  invFun z := z - c • w
  left_inv r := by simp
  right_inv z := by simp




/-! ### Amplification with challenge space of size `q` -/

section Amplification

variable (s : LinStatement q V W) (n : ℕ)

/-- A prover for the `n`-fold parallel repetition with field challenges. -/
structure LinParallelProver (q : ℕ) (V W : Type*) (n : ℕ) where
  commitments : Fin n → W
  respond : (Fin n → ZMod q) → (Fin n → V)

/-- The parallel verifier accepts iff all rounds accept. -/
def LinParallelAccepts (P : LinParallelProver q V W n) (c : Fin n → ZMod q) : Prop :=
  ∀ i, LinAccepts s ⟨P.commitments i, c i, P.respond c i⟩


open scoped Classical in
/-- The set of challenge vectors the prover can answer. -/
noncomputable def linCheatSet (P : LinParallelProver q V W n) : Finset (Fin n → ZMod q) :=
  Finset.univ.filter (fun c => LinParallelAccepts s n P c)




/-- The honest parallel prover. -/
def linHonestProver (w : V) (r : Fin n → V) : LinParallelProver q V W n where
  commitments := fun i => s.hom (r i)
  respond := fun c i => r i + (c i) • w



end Amplification


/-! ### A decidable instance over `ZMod 5` -/

section Example

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- A true linear statement over the field with five elements: `w = 3`. -/
def idStatement : LinStatement 5 (ZMod 5) (ZMod 5) := ⟨LinearMap.id, 3⟩

/-- A false linear statement: the zero map cannot hit the target `1`. -/
def zeroStatement : LinStatement 5 (ZMod 5) (ZMod 5) := ⟨0, 1⟩





end Example

end ZeroKnowledgeTheoremProving.LinearSigma


