-- Prove2me | Definitions.Def_Novelty_DiagonalPlethysmGroup
-- name    : Novelty_DiagonalPlethysmGroup
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:14:04.795178+00:00
-- url     : https://prove2.me/theorems/981ec258-1e5d-43ec-995c-7ee664bb864c
-- title:
--   Aether Catalog definitions — Novelty_DiagonalPlethysmGroup
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.DiagonalPlethysmGroup`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/DiagonalPlethysmGroup.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The abelian group of diagonal plethysms on the odd power-sum ring

This file is the research *extension* of the cycle
"Plethystic Triviality of the Shifted `t`-Schur Basis"
(`PlethysticTrivialityShiftedTSchur`, `OddPowerSumPlethysm`).

The two companion files study a *single* plethystic operator
`φ_t : p_{2k+1} ↦ (1 - t^{2k+1}) p_{2k+1}` and its inverse
`ψ_t : p_{2k+1} ↦ p_{2k+1} / (1 - t^{2k+1})`, proving the headline identity
`S^t_λ = φ_t(Q_λ)` and the triviality statement that `φ_t` is an automorphism.

Here we identify the *structural reason* behind triviality: both `φ_t` and `ψ_t`
are instances of a single construction, the **diagonal plethysm** `Φ w` attached to a
"weight" `w : ℕ → K`, sending `p_{2k+1} ↦ w(k) · p_{2k+1}`.  The new content is:

* `Phi_comp` — composition law `Φ v ∘ Φ w = Φ (v · w)`: the diagonal plethysms form a
  *commutative monoid* under composition, with `Φ 1 = id` (`Phi_one`).
* `PhiEquiv` — whenever every weight is a unit (`w k ≠ 0`), `Φ w` is an algebra
  *automorphism*, with inverse `Φ (w⁻¹)`.  This single result subsumes the
  invertibility of `φ_t` and `ψ_t`.
* `phiT_eq_Phi`, `psiT_eq_Phi`, `phiT_psiT_eq_id` — `φ_t = Φ cc`, `ψ_t = Φ dd`, and the
  inverse relation `φ_t ∘ ψ_t = id` is recovered *abstractly* from `Phi_comp` together
  with the pointwise identity `cc k · dd k = 1`.
* `Phi_ne_id_of_weight_ne_one` — `Φ w ≠ id` as soon as a single weight differs from `1`,
  pinpointing the exact non-triviality boundary at the level of the whole group.
* `Phi_monomial_pow` — diagonality on each variable-power.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer):  `φ_t` and `ψ_t` are not two separate operators but two
  points of a one-parameter (indeed function-valued) family `w ↦ Φ w` that is a group
  homomorphism from the units `(ℕ → K)ˣ` into `Aut(Λ)`; triviality of the `t`-Schur basis
  is then a corollary of group structure, not a coincidence of two ad-hoc inverses.
Experiment (Experimenter):  Define `Φ w = aeval (k ↦ C (w k) · X k)` and prove the
  composition law on generators via `MvPolynomial.algHom_ext`, then `ring`.  Recover the
  two existing operators by `cc`/`dd` substitution and re-derive their inverse relation
  from `cc k * dd k = 1` (uses `cc_ne`).
Analysis (Analyst):  The monoid map `w ↦ Φ w` restricts to a *group* homomorphism on the
  pointwise units; `φ_t` lives in the image of the unit `cc`, so its inverse is forced.
  The deformation's content is exactly the diagonal of scalars `w`, nothing more.
Critique (Critic):  Group-theoretic triviality could still be vacuous if `Φ` collapsed
  weights; we prove `Φ` is *injective enough* — `Φ w = id ⇒ w k = 1 (∀k)` — via evaluation,
  ruling out a degenerate parametrization, and confirm `Φ cc ≠ id`.
Synthesis (PI):  Diagonal plethysms form a commutative group acting faithfully on the odd
  power-sum ring; `φ_t` is one element of it, so "plethystic triviality" is the statement
  that the `t`-Schur basis is the `Φ cc`-image of the Schur-`Q` basis.
-- !-- end Lab Notes -- !--
-/

open MvPolynomial

noncomputable section

namespace DiagonalPlethysmGroup

/-- The base field `K = ℚ(t)`. -/
abbrev K := RatFunc ℚ

/-- The odd power-sum ring `MvPolynomial ℕ K`, with `X k` standing for `p_{2k+1}`. -/
abbrev Lam := MvPolynomial ℕ K

/-- The transcendental parameter `t ∈ K`. -/
def tt : K := RatFunc.X

/-- The scalar `c_k = 1 - t^{2k+1}` (the `φ_t` weight). -/
def cc (k : ℕ) : K := 1 - tt ^ (2 * k + 1)


/-- The inverse scalar `d_k = 1 / (1 - t^{2k+1})` (the `ψ_t` weight). -/
def dd (k : ℕ) : K := 1 / cc k


/-! ### The diagonal plethysm attached to a weight -/

/-- The **diagonal plethysm** `Φ w : p_{2k+1} ↦ w(k) · p_{2k+1}` attached to a weight
`w : ℕ → K`, as a `K`-algebra endomorphism of the odd power-sum ring. -/
def Phi (w : ℕ → K) : Lam →ₐ[K] Lam :=
  MvPolynomial.aeval (fun k => MvPolynomial.C (w k) * X k)

@[simp] lemma Phi_X (w : ℕ → K) (k : ℕ) : Phi w (X k) = MvPolynomial.C (w k) * X k := by
  simp [Phi]

/-
`Φ 1 = id`: the unit weight gives the identity plethysm.
-/
lemma Phi_one : Phi (fun _ => (1 : K)) = AlgHom.id K Lam := by
  ext k; simp [Phi]

/-
**Composition law.** `Φ v ∘ Φ w = Φ (v · w)`: the diagonal plethysms form a
commutative monoid under composition.
-/
lemma Phi_comp (v w : ℕ → K) :
    (Phi v).comp (Phi w) = Phi (fun k => v k * w k) := by
  ext;
  simp +decide [ mul_left_comm, MvPolynomial.C_mul' ]


/-- When every weight `w k` is a unit, `Φ w` is an algebra **automorphism** with inverse
`Φ (fun k => (w k)⁻¹)`. -/
def PhiEquiv (w : ℕ → K) (hw : ∀ k, w k ≠ 0) : Lam ≃ₐ[K] Lam :=
  AlgEquiv.ofAlgHom (Phi w) (Phi (fun k => (w k)⁻¹))
    (by
      rw [show (Phi w).comp (Phi (fun k => (w k)⁻¹)) = Phi (fun k => w k * (w k)⁻¹) from
            Phi_comp _ _]
      have : (fun k => w k * (w k)⁻¹) = (fun _ => (1 : K)) := by
        funext k; field_simp [hw k]
      rw [this, Phi_one])
    (by
      rw [show (Phi (fun k => (w k)⁻¹)).comp (Phi w) = Phi (fun k => (w k)⁻¹ * w k) from
            Phi_comp _ _]
      have : (fun k => (w k)⁻¹ * w k) = (fun _ => (1 : K)) := by
        funext k; field_simp [hw k]
      rw [this, Phi_one])


/-! ### Diagonality on monomials -/

/-
`Φ w` scales each variable-power diagonally: `Φ w (p_n^m) = w(k)^m · p_n^m`.
-/

/-! ### Recovering `φ_t` and `ψ_t` -/

/-- The shifted-`t`-Schur plethysm `φ_t` is the diagonal plethysm with weight `cc`. -/
def phiT : Lam →ₐ[K] Lam := Phi cc

/-- The inverse plethysm `ψ_t` is the diagonal plethysm with weight `dd`. -/
def psiT : Lam →ₐ[K] Lam := Phi dd




/-! ### Non-triviality boundary -/

/-
If `Φ w = id` then every weight equals `1`. This shows the parametrization
`w ↦ Φ w` is faithful (no degenerate collapse).
-/


/-
`cc 0 = 1 - t ≠ 1`, since `t = RatFunc.X ≠ 0`.
-/


end DiagonalPlethysmGroup


