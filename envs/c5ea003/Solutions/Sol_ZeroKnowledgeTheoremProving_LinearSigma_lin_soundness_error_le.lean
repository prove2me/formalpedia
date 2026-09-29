-- Prove2me | solution 1 for ZeroKnowledgeTheoremProving.LinearSigma.lin_soundness_error_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T12:31:30.013757+00:00
-- url     : https://prove2.me/submissions/61685d1c-ba51-4343-abe2-9e878b0debc0

-- Sol generated from Applications/ZeroKnowledgeTheoremProving/LargeChallengeSpace.lean
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











/-- **Linear special soundness.** Two accepting responses at one commitment for
*any two distinct* challenges determine the witness, by solving a linear
equation over the field `ZMod q`. -/
theorem lin_special_soundness (s : LinStatement q V W) (a : W) {c c' : ZMod q}
    (hne : c ≠ c') (z z' : V)
    (h : LinAccepts s ⟨a, c, z⟩) (h' : LinAccepts s ⟨a, c', z'⟩) :
    LinIsWitness s ((c - c')⁻¹ • (z - z')) := by
  haveI : Fact (Nat.Prime q) := ‹_›
  have hz : s.hom z = a + c • s.target := h
  have hz' : s.hom z' = a + c' • s.target := h'
  have hsub : s.hom (z - z') = (c - c') • s.target := by
    rw [map_sub, hz, hz', sub_smul]
    abel
  have hne' : c - c' ≠ 0 := sub_ne_zero_of_ne hne
  show s.hom ((c - c')⁻¹ • (z - z')) = s.target
  rw [map_smul, hsub, smul_smul, inv_mul_cancel₀ hne', one_smul]

/-! ### Amplification with challenge space of size `q` -/


variable (s : LinStatement q V W) (n : ℕ)



/-- With no witness a committed prover can satisfy at most one challenge
vector. -/
theorem lin_parallel_unique_of_no_witness (hno : ∀ w : V, ¬ LinIsWitness s w)
    (P : LinParallelProver q V W n) {c c' : Fin n → ZMod q}
    (hc : LinParallelAccepts s n P c) (hc' : LinParallelAccepts s n P c') :
    c = c' := by
  funext i
  by_contra hne
  exact hno _ (lin_special_soundness s (P.commitments i) hne (P.respond c i) (P.respond c' i)
    (hc i) (hc' i))


open scoped Classical in
/-- Without a witness the cheating set has at most one element. -/
theorem linCheatSet_card_le_one (hno : ∀ w : V, ¬ LinIsWitness s w)
    (P : LinParallelProver q V W n) :
    (linCheatSet s n P).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [linCheatSet, Finset.mem_filter] at ha hb
  exact lin_parallel_unique_of_no_witness s n hno P ha.2 hb.2

/-- There are `q ^ n` challenge vectors. -/
theorem lin_card_challenge_vectors :
    (Finset.univ : Finset (Fin n → ZMod q)).card = q ^ n := by
  haveI : NeZero q := ⟨(Fact.out : Nat.Prime q).ne_zero⟩
  simp [ZMod.card]







/-! ### A decidable instance over `ZMod 5` -/











open ZeroKnowledgeTheoremProving.LinearSigma in
open scoped Classical in
theorem solution(hno : ∀ w : V, ¬ LinIsWitness s w)
    (P : LinParallelProver q V W n) :
    ((linCheatSet s n P).card : ℚ) / (Finset.univ : Finset (Fin n → ZMod q)).card
      ≤ (1 / q : ℚ) ^ n := by
  have hq : 0 < q := (Fact.out : Nat.Prime q).pos
  have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have h2 : (0 : ℚ) < (q : ℚ) ^ n := by positivity
  rw [lin_card_challenge_vectors n]
  rw [div_le_iff₀ (by exact_mod_cast h2)]
  have hcard : ((linCheatSet s n P).card : ℚ) ≤ 1 := by
    exact_mod_cast linCheatSet_card_le_one s n hno P
  calc ((linCheatSet s n P).card : ℚ) ≤ 1 := hcard
    _ = (1 / q : ℚ) ^ n * (q : ℚ) ^ n := by
        rw [div_pow, one_pow, div_mul_cancel₀]
        exact ne_of_gt h2
    _ = (1 / q : ℚ) ^ n * ((q ^ n : ℕ) : ℚ) := by push_cast; ring
