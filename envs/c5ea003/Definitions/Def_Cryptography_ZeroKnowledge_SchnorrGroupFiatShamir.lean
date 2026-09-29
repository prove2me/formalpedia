-- Prove2me | Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupFiatShamir
-- name    : Cryptography_ZeroKnowledge_SchnorrGroupFiatShamir
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:30:56.292415+00:00
-- url     : https://prove2.me/theorems/e232e819-9cac-4809-aab0-af1421655102
-- title:
--   Aether Catalog definitions — Cryptography_ZeroKnowledge_SchnorrGroupFiatShamir
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.ZeroKnowledge.SchnorrGroupFiatShamir`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/ZeroKnowledge/SchnorrGroupFiatShamir.lean by skeleton subtraction
import Mathlib
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

namespace SchnorrGrp

variable {G : Type*} [CommGroup G] {q : ℕ} {M : Type*}

/-- A non-interactive Fiat–Shamir proof: a commitment and a response.  The challenge is not
transmitted since the verifier recomputes it from the oracle. -/
@[ext]
structure FSProof (G : Type*) (q : ℕ) where
  /-- The commitment. -/
  a : G
  /-- The response. -/
  z : ZMod q

/-- The Fiat–Shamir verifier: recompute the challenge `H (pub, a, m)` and run the
interactive verifier on the resulting transcript. -/
def FSAccepts (g pub : G) (H : G × G × M → ZMod q) (m : M) (π : FSProof G q) : Prop :=
  Accepts g pub ⟨π.a, H (pub, π.a, m), π.z⟩

/-- The honest non-interactive prover: commit to `g ^ r`, hash, and respond. -/
def fsProve (g : G) (H : G × G × M → ZMod q) (m : M) (x r : ZMod q) : FSProof G q :=
  ⟨gexp g r, r + H (gexp g x, gexp g r, m) * x⟩



/-! ### Forking: witness extraction in the random-oracle model -/



/-! ### Programming the random oracle: zero knowledge of the transform -/

/-- The simulator's non-interactive proof for a chosen challenge `c` and response `z`. -/
def fsSimulate (g pub : G) (c z : ZMod q) : FSProof G q :=
  ⟨gexp g z * (gexp pub c)⁻¹, z⟩

open scoped Classical in
/-- The oracle reprogrammed at the single point invented by the simulator. -/
noncomputable def progOracle (pub : G) (H : G × G × M → ZMod q) (m : M) (c z : ZMod q)
    (g : G) : G × G × M → ZMod q :=
  Function.update H (pub, (fsSimulate g pub c z).a, m) c



/-- The joint randomness bijection `(r, c) ↦ (r + c * x, c)`. -/
def fsZKEquiv (x : ZMod q) : ZMod q × ZMod q ≃ ZMod q × ZMod q where
  toFun rc := (rc.1 + rc.2 * x, rc.2)
  invFun zc := (zc.1 - zc.2 * x, zc.2)
  left_inv := by intro rc; simp
  right_inv := by intro zc; simp


/-! ### Quantitative security in the random-oracle model -/




end SchnorrGrp


