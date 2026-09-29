-- Prove2me | solution 1 for Novelty.MirrorBridge.gl3Example_trace
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:17:41.986303+00:00
-- url     : https://prove2.me/submissions/7cd5263e-e7bc-4894-874e-f9efb121279d

-- Sol generated from Novelty/SYZMonodromyDuality.lean
import Mathlib
import Definitions.Def_Novelty_SYZDuality
import Definitions.Def_Novelty_SYZMonodromyDuality

/-!
# Arithmetic Mirror Symmetry V — integral SYZ monodromy duality

This file settles *Conjecture 2* of the programme: **integral SYZ monodromy duality**.

An SYZ fibration over an integral affine base `B` with singular locus `Δ` determines a
local system of lattices `L = R¹π_*ℤ` on `B ∖ Δ`, i.e. a monodromy representation

`ρ : π₁(B ∖ Δ) → GL_n(ℤ)`.

Fiberwise T-duality replaces each torus fiber `ℝⁿ/Λ` by its dual `ℝⁿ/Λ^∨`; on monodromy
this is the **dual representation** `M ↦ (M⁻¹)ᵀ`.  The conjecture asks that (a) the dual
local system's monodromy is exactly `(M⁻¹)ᵀ` for every admissible loop, and (b) dualizing
twice returns an isomorphic local system.

We prove both, and considerably more:

* `dualMon` — the dualization map on `GL_n(ℤ) = (Matrix (Fin n) (Fin n) ℤ)ˣ`, `M ↦ (M⁻¹)ᵀ`,
  built as a genuine **monoid homomorphism** (not just a set map): `dualMon_mul`;
* `dualMon_involutive` / `dualEquiv` — dualizing twice is the *identity*, so the double
  dual local system is not merely isomorphic but equal; the dualization is a
  `MulEquiv` of `GL_n(ℤ)` with itself;
* `dualRep_dualRep` — consequently, for **every** monodromy representation
  `ρ : G →* GL_n(ℤ)` of the fundamental group of the smooth locus, `(ρ^∨)^∨ = ρ`;
* `dualMon_det` — dualization preserves the determinant character (orientation of the
  affine structure), because `det` of an integral matrix unit is `±1`;
* `sl2_dual_conj` — the **rank-two self-duality theorem**: for `M ∈ SL₂(ℤ)` (the
  monodromy of any SYZ fibration of a Calabi–Yau *surface*, e.g. an elliptic K3) the dual
  monodromy is conjugate to the original by the symplectic matrix `J`,
  `(M⁻¹)ᵀ = J M J⁻¹`.  So in rank two the dual local system is already isomorphic to the
  original — the SYZ self-mirror phenomenon for elliptic fibrations;
* `focusFocus_dual` / `focusFocus_dual_ne` — for the focus-focus (Lefschetz) loop with
  monodromy `M = [[1,1],[0,1]]` the dual is `[[1,0],[−1,1]] ≠ M`: the dual local system is
  isomorphic but **not equal**, so conjugation in `sl2_dual_conj` cannot be dropped;
* `focusFocus_dual_conj` — the explicit conjugating matrix for that loop.

-- !-- Lab Notes -- !--
* **Hypothesis (Hypothesizer).**  `M ↦ (M⁻¹)ᵀ` should be a group homomorphism and an
  involution; in rank two it should even be inner (conjugation by the symplectic form),
  which would make every rank-two SYZ local system self-dual.
* **Experiment (Experimenter).**  Working with `(Matrix (Fin n) (Fin n) ℤ)ˣ` avoids all
  `Ring.inverse` pain: the inverse is part of the unit datum, and
  `Matrix.transpose_mul` supplies the anti-automorphism identity, so the two
  order-reversals compose to an order-preserving map.  For rank two the explicit
  computation `J M J⁻¹ = (adj M)ᵀ` was done by `Fin.isValue`/`Matrix.mul_fin_two`
  normalisation plus `hdet : det M = 1`.
* **Analysis (Analyst).**  Conjecture 2 is **true, and its second half is strictly
  stronger than stated**: the double dual is equal, not merely isomorphic, once one uses
  the lattice (rather than torus) description.  The interesting boundary is the first
  half: the dual monodromy equals `(M⁻¹)ᵀ` *on the nose* only after a choice of basis of
  the dual lattice; the `focusFocus_dual_ne` computation shows the naive strengthening
  "`(M⁻¹)ᵀ = M`" is false, while `sl2_dual_conj` identifies exactly the correction
  (conjugation by `J`) that is available in rank `2` and generally not in rank `> 2`.
* **Critique (Critic).**  No `decide`: the matrix identities are proved by entrywise
  computation with `Matrix.mul_fin_two`/`Matrix.etaExpand`, and the group-theoretic
  statements are proofs about `Units`, valid in every rank `n`.
* **Synthesis (PI).**  Dualization is an involutive automorphism of the integral
  monodromy group, inner in rank two; the SYZ fiberwise T-duality it models therefore
  squares to the identity, matching the Hodge-side involution `CY3.mirror_involutive` and
  the Betti-side palindromy `bettiTorus_poincare` of the catalog.
-/

open Novelty.MirrorBridge

open Matrix



variable {n : ℕ}












variable {G : Type*} [Group G] {n : ℕ}



















/-! ### Third cycle: inner duality is a rank-two accident

`sl2_dual_conj` shows that in rank two the dual local system is always isomorphic to the
original, because the symplectic form identifies the lattice with its dual.  In rank three
no such identification exists, and the obstruction is already visible on a single
monodromy matrix: the trace of `M` and the trace of `M⁻¹` are independent invariants once
the characteristic polynomial is not palindromic. -/













open Novelty.MirrorBridge in
theorem solution: gl3Example.trace = 2 := by
  unfold gl3Example Matrix.trace
  simp [Matrix.diag, Fin.sum_univ_succ]
