-- Prove2me | solution 1 for SchnorrGrp.card_filter_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:01:04.758359+00:00
-- url     : https://prove2.me/submissions/ca2fe303-f621-40d3-b28e-48aae05a87e4

-- Sol generated from Cryptography/ZeroKnowledge/SchnorrGroupFiatShamir.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupFiatShamir
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol
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
theorem solution[NeZero q] {Q : ℕ} (i : Fin Q) (v : ZMod q) :
    (Finset.univ.filter (fun f : Fin Q → ZMod q => f i = v)).card * q
      = Fintype.card (Fin Q → ZMod q) := by
  classical
  have key : ∀ w : ZMod q,
      (Finset.univ.filter (fun f : Fin Q → ZMod q => f i = w)).card
        = (Finset.univ.filter (fun f : Fin Q → ZMod q => f i = v)).card := by
    intro w
    refine Finset.card_bij (fun f _ => Function.update f i v) ?_ ?_ ?_
    · intro f _; simp
    · intro f₁ h₁ f₂ h₂ he
      simp only [Finset.mem_filter] at h₁ h₂
      funext j
      by_cases hj : j = i
      · subst hj; rw [h₁.2, h₂.2]
      · have h3 := congrFun he j
        simp only [Function.update_of_ne hj] at h3
        exact h3
    · intro f hf
      simp only [Finset.mem_filter] at hf
      exact ⟨Function.update f i w, by simp, by
        funext j
        by_cases hj : j = i
        · subst hj; simp [hf.2]
        · simp [Function.update_of_ne hj]⟩
  have hcards : Fintype.card (Fin Q → ZMod q)
      = ∑ w : ZMod q, (Finset.univ.filter (fun f : Fin Q → ZMod q => f i = w)).card := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise (fun f _ => Finset.mem_univ (f i))
  rw [hcards]
  simp only [key]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, ZMod.card, mul_comm]
