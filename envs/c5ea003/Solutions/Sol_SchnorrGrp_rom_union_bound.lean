-- Prove2me | solution 1 for SchnorrGrp.rom_union_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:03:02.941487+00:00
-- url     : https://prove2.me/submissions/c06aef33-9c08-4c42-9a7b-10222bf14f8f

-- Sol generated from Cryptography/ZeroKnowledge/SchnorrGroupFiatShamir.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupFiatShamir
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol
import Theorems.Thm_SchnorrGrp_accepting_challenges_card_le_one
import Theorems.Thm_SchnorrGrp_card_filter_apply_eq
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Fiat–Shamir for group-model Schnorr, and its analysis in the random-oracle model

Building on `Cryptography.ZeroKnowledge.SchnorrGroupProtocol` (the faithful cyclic-group
model of the Schnorr Σ-protocol), this file performs the **Fiat–Shamir transform**: the
verifier's challenge is replaced by the value of a hash function `H` on the statement, the
commitment and the message, turning the protocol into a non-interactive proof — a Schnorr
signature.

The random oracle is modelled as an arbitrary function `H : G × G × M → ZMod q`; the two
random-oracle techniques are formalised explicitly:

* **programmability** (`fs_sim_accepts`, `progOracle_agrees_off`): the zero-knowledge
  simulator reprograms `H` at the single point `(pub, a, m)` it invented, and its output is
  then a valid proof; the reprogrammed oracle is indistinguishable from `H` for anyone who
  never queries that point.
* **rewinding / forking** (`fs_forking_extraction`, `fs_fork_update_extraction`): two
  accepting proofs sharing a commitment but obtained under two oracle answers extract the
  secret key, which is exactly the algebraic engine of the Forking Lemma.

## Main results

* `fs_completeness` — the honest non-interactive prover is accepted for **every** oracle.
* `fs_accepts_iff_interactive` — Fiat–Shamir verification *is* interactive verification with
  the challenge fixed to the oracle's answer.
* `fs_forking_extraction`, `fs_fork_update_extraction` — forking extraction of the witness.
* `fs_sim_accepts`, `progOracle_agrees_off` — the programmed simulator produces accepting
  proofs and only touches the oracle at one point.
* `fs_zk_pmf` — perfect zero knowledge of the transform against a uniformly random oracle
  answer: honest and simulated transcript distributions are equal.
* `rom_forgery_bound` — an adversary that fixes `(a, z)` before the oracle answers at
  `(pub, a, m)` forges with probability at most `1 / q`.
* `rom_union_bound` — an adversary making `Q` oracle queries and precommitting to one
  candidate response per query forges with probability at most `Q / q`.
-/

open SchnorrGrp

variable {G : Type*} [CommGroup G] {q : ℕ} {M : Type*}






/-! ### Forking: witness extraction in the random-oracle model -/



/-! ### Programming the random oracle: zero knowledge of the transform -/







/-! ### Quantitative security in the random-oracle model -/





open SchnorrGrp in
open scoped Classical in
theorem solution[Fact q.Prime] {g pub : G} (hpub : pub ^ q = 1) (hpub1 : pub ≠ 1)
    (Q : ℕ) (a : Fin Q → G) (z : Fin Q → ZMod q) :
    ((Finset.univ.filter (fun f : Fin Q → ZMod q =>
        ∃ i, Accepts g pub ⟨a i, f i, z i⟩)).card : ℚ)
        / (Fintype.card (Fin Q → ZMod q)) ≤ Q / q := by
  classical
  set N := Fintype.card (Fin Q → ZMod q) with hN
  set S := Finset.univ.filter (fun f : Fin Q → ZMod q => ∃ i, Accepts g pub ⟨a i, f i, z i⟩)
    with hS
  set T := fun i : Fin Q =>
    Finset.univ.filter (fun f : Fin Q → ZMod q => Accepts g pub ⟨a i, f i, z i⟩) with hT
  -- each `T i` occupies at most a `1/q` fraction
  have hTi : ∀ i, (T i).card * q ≤ N := by
    intro i
    obtain ⟨c₀, hc₀⟩ := Finset.card_le_one_iff_subset_singleton.mp
      (accepting_challenges_card_le_one hpub hpub1 (a i) (z i))
    have hsub : T i ⊆ Finset.univ.filter (fun f : Fin Q → ZMod q => f i = c₀) := by
      intro f hf
      simp only [hT, Finset.mem_filter] at hf
      have : f i ∈ Finset.univ.filter (fun c : ZMod q => Accepts g pub ⟨a i, c, z i⟩) := by
        simp [hf.2]
      simpa using hc₀ this
    calc (T i).card * q
        ≤ (Finset.univ.filter (fun f : Fin Q → ZMod q => f i = c₀)).card * q :=
          Nat.mul_le_mul_right _ (Finset.card_le_card hsub)
      _ = N := card_filter_apply_eq i c₀
  -- union bound
  have hSsub : S ⊆ Finset.univ.biUnion T := by
    intro f hf
    simp only [hS, Finset.mem_filter] at hf
    obtain ⟨i, hi⟩ := hf.2
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by simp [hT, hi]⟩
  have hcard : S.card * q ≤ Q * N := by
    have h1 : S.card ≤ ∑ i : Fin Q, (T i).card :=
      le_trans (Finset.card_le_card hSsub) (Finset.card_biUnion_le)
    calc S.card * q ≤ (∑ i : Fin Q, (T i).card) * q := Nat.mul_le_mul_right _ h1
      _ = ∑ i : Fin Q, (T i).card * q := by rw [Finset.sum_mul]
      _ ≤ ∑ _i : Fin Q, N := Finset.sum_le_sum (fun i _ => hTi i)
      _ = Q * N := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- convert to rationals
  have hq : (0 : ℚ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have hNpos : (0 : ℚ) < N := by
    have : 0 < N := Fintype.card_pos
    exact_mod_cast this
  rw [div_le_div_iff₀ hNpos hq]
  have : (S.card : ℚ) * q ≤ Q * N := by exact_mod_cast hcard
  linarith
