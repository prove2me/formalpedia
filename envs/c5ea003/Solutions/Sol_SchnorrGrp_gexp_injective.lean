-- Prove2me | solution 1 for SchnorrGrp.gexp_injective
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:59:22.594083+00:00
-- url     : https://prove2.me/submissions/3d24f63f-e897-4ac5-9616-d9be8a74e551

-- Sol generated from Cryptography/ZeroKnowledge/SchnorrGroupProtocol.lean
import Mathlib
import Definitions.Def_Cryptography_ZeroKnowledge_SchnorrGroupProtocol
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Schnorr identification Σ-protocol in a genuine cyclic group

The catalog already contains an *additive* model of Schnorr (`Cryptography.SchnorrIdentification`
and the files in `Cryptography/ZeroKnowledge/`), where the "group" is the field `ZMod p`,
"scalar multiplication" is field multiplication and the public key of `x` is `x * g`.  That
model is algebraically convenient but it hides the actual group-theoretic content of the
protocol: in the real scheme the prover works in a cyclic group `G` of prime order `q`, the
commitment is `g ^ r`, the public key is `g ^ x`, and verification reads `g ^ z = a * pub ^ c`
with the exponents living in `ZMod q` while the group operation lives in `G`.

This file develops that faithful multiplicative model:

* `gexp h e = h ^ e.val` is exponentiation of a group element by a `ZMod q` scalar; it is
  well defined as a homomorphism precisely on the `q`-torsion (`h ^ q = 1`), which is the
  standing hypothesis throughout.
* `SchnorrGrp.Accepts g pub T` is the verification equation `g ^ z = a * pub ^ c`.

## Main results

* `gexp_add`, `gexp_mul`, `gexp_sub`, `gexp_injective` — the exponentiation API.
* `completeness` — the honest prover `(g ^ r, c, r + c * x)` is always accepted.
* `special_soundness_witness` — two accepting transcripts sharing a commitment with distinct
  challenges yield a genuine discrete logarithm of an *arbitrary* public key `pub`
  (only `pub ^ q = 1` is needed), i.e. knowledge soundness with extractor
  `(z₁ - z₂) * (c₁ - c₂)⁻¹`.
* `special_soundness_eq_witness` — specialised to `pub = g ^ x`, the extractor returns `x`.
* `simulate_accepts`, `honest_eq_simulate`, `hvzk_equiv`, `hvzk_pmf` — perfect
  honest-verifier zero knowledge: the simulator's output is accepting, matches the honest
  transcript under an explicit bijection of the randomness, and induces *literally the same
  distribution* as the honest prover (equality of `PMF`s).
* `accepting_challenges_card_le_one`, `soundness_error_le` — the quantitative soundness
  error: a commitment/response pair fixed in advance is accepted for at most one challenge,
  so a cheating prover succeeds with probability at most `1 / q`.
-/

open SchnorrGrp

variable {G : Type*} [CommGroup G] {q : ℕ}

/-! ### Exponentiation by a `ZMod q` scalar -/


/-- On a `q`-torsion element, `h ^ ·` only depends on the exponent modulo `q`. -/
theorem pow_congr_of_modEq {h : G} (hh : h ^ q = 1) {m n : ℕ} (hmn : m ≡ n [MOD q]) :
    h ^ m = h ^ n :=
  pow_eq_pow_iff_modEq.mpr (hmn.of_dvd (orderOf_dvd_iff_pow_eq_one.mpr hh))

@[simp] theorem gexp_zero (h : G) [NeZero q] : gexp h (0 : ZMod q) = 1 := by
  simp [gexp]


theorem gexp_add [NeZero q] {h : G} (hh : h ^ q = 1) (e₁ e₂ : ZMod q) :
    gexp h (e₁ + e₂) = gexp h e₁ * gexp h e₂ := by
  rw [gexp, gexp, gexp, ← pow_add]
  exact pow_congr_of_modEq hh (by rw [ZMod.val_add]; exact Nat.mod_modEq _ q)



theorem gexp_neg [NeZero q] {h : G} (hh : h ^ q = 1) (e : ZMod q) :
    gexp h (-e) = (gexp h e)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← gexp_add hh, neg_add_cancel, gexp_zero]

theorem gexp_sub [NeZero q] {h : G} (hh : h ^ q = 1) (e₁ e₂ : ZMod q) :
    gexp h (e₁ - e₂) = gexp h e₁ * (gexp h e₂)⁻¹ := by
  rw [sub_eq_add_neg, gexp_add hh, gexp_neg hh]


/-- For a generator of order exactly `q`, `gexp g` kills only the zero exponent. -/
theorem gexp_eq_one_iff [NeZero q] {g : G} (hg : orderOf g = q) (e : ZMod q) :
    gexp g e = 1 ↔ e = 0 := by
  refine ⟨fun h => ?_, by rintro rfl; simp⟩
  have hd : orderOf g ∣ e.val := orderOf_dvd_iff_pow_eq_one.mpr h
  rw [hg] at hd
  exact (ZMod.val_eq_zero e).mp (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt e))



/-! ### The protocol -/










/-! ### Honest-verifier zero knowledge -/







/-! ### Quantitative soundness error -/




open SchnorrGrp in
theorem solution[NeZero q] {g : G} (hg : orderOf g = q) :
    Function.Injective (gexp g : ZMod q → G) := by
  have hgq : g ^ q = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  intro a b hab
  have h1 : gexp g (a - b) = 1 := by rw [gexp_sub hgq, hab, mul_inv_cancel]
  exact sub_eq_zero.mp ((gexp_eq_one_iff hg _).mp h1)
