-- Prove2me | Definitions.Def_Novelty_SYZMonodromyDuality
-- name    : Novelty_SYZMonodromyDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:40:06.373135+00:00
-- url     : https://prove2.me/theorems/18b1e534-fb8a-40b7-b002-d0a3144df2c6
-- title:
--   Aether Catalog definitions — Novelty_SYZMonodromyDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SYZMonodromyDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SYZMonodromyDuality.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_SYZDuality

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

namespace Novelty.MirrorBridge

open Matrix

/-- The integral monodromy group `GL_n(ℤ)` of an SYZ local system of lattices. -/
abbrev IntGL (n : ℕ) := (Matrix (Fin n) (Fin n) ℤ)ˣ

section Dual

variable {n : ℕ}

/-- **Fiberwise T-duality on monodromy.**  Dualizing the torus fibers sends a monodromy
matrix `M` to `(M⁻¹)ᵀ`, the matrix of the transpose-inverse action on the dual lattice. -/
def dualMon (M : IntGL n) : IntGL n where
  val := (↑M⁻¹ : Matrix (Fin n) (Fin n) ℤ)ᵀ
  inv := (↑M : Matrix (Fin n) (Fin n) ℤ)ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul]
    simp
  inv_val := by
    rw [← Matrix.transpose_mul]
    simp


/-- Dualization preserves the identity monodromy (the trivial loop). -/
@[simp] theorem dualMon_one : dualMon (1 : IntGL n) = 1 := by
  ext i j
  simp [dualMon]

/-- **Dualization is a homomorphism of monodromy groups.**  Composing loops before or
after dualizing gives the same answer: the two order reversals (inverse and transpose)
cancel. -/
theorem dualMon_mul (M N : IntGL n) : dualMon (M * N) = dualMon M * dualMon N := by
  ext i j
  simp [dualMon, Matrix.transpose_mul, _root_.mul_inv_rev]

/-- Dualization packaged as a monoid homomorphism `GL_n(ℤ) →* GL_n(ℤ)`. -/
def dualHom : IntGL n →* IntGL n where
  toFun := dualMon
  map_one' := dualMon_one
  map_mul' := dualMon_mul

/-- **Dualizing twice is the identity.**  The double dual local system is equal (hence a
fortiori isomorphic) to the original. -/
@[simp] theorem dualMon_involutive (M : IntGL n) : dualMon (dualMon M) = M := by
  ext i j
  simp [dualMon]

/-- Dualization as a group automorphism of `GL_n(ℤ)` of order dividing two. -/
def dualEquiv : IntGL n ≃* IntGL n where
  toFun := dualMon
  invFun := dualMon
  left_inv := dualMon_involutive
  right_inv := dualMon_involutive
  map_mul' := dualMon_mul



end Dual

section Representation

variable {G : Type*} [Group G] {n : ℕ}

/-- The dual monodromy representation of the SYZ local system: post-compose the
representation of `π₁(B ∖ Δ)` with fiberwise dualization. -/
def dualRep (ρ : G →* IntGL n) : G →* IntGL n := dualHom.comp ρ



end Representation

section Rank2

/-- The symplectic form on the rank-two lattice, `J = [[0, −1], [1, 0]]`. -/
def symplJ : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

/-- The inverse symplectic matrix `J⁻¹ = [[0, 1], [−1, 0]]`. -/
def symplJinv : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]



/-- The **focus-focus (Lefschetz) monodromy** of an SYZ fibration around a nodal fiber. -/
def focusFocus : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 0, 1]

/-- Its inverse, the monodromy of the reversed loop. -/
def focusFocusInv : Matrix (Fin 2) (Fin 2) ℤ := !![1, -1; 0, 1]






end Rank2

section Rank3

/-! ### Third cycle: inner duality is a rank-two accident

`sl2_dual_conj` shows that in rank two the dual local system is always isomorphic to the
original, because the symplectic form identifies the lattice with its dual.  In rank three
no such identification exists, and the obstruction is already visible on a single
monodromy matrix: the trace of `M` and the trace of `M⁻¹` are independent invariants once
the characteristic polynomial is not palindromic. -/

/-- A rank-three monodromy matrix: the companion matrix of `x³ − 2x² + x − 1`, an element of
`SL₃(ℤ)` whose characteristic polynomial is *not* palindromic. -/
def gl3Example : Matrix (Fin 3) (Fin 3) ℤ := !![0, 0, 1; 1, 0, -1; 0, 1, 2]

/-- Its inverse `M⁻¹ = M² − 2M + 1`, computed from the Cayley–Hamilton relation. -/
def gl3ExampleInv : Matrix (Fin 3) (Fin 3) ℤ := !![1, 1, 0; -2, 0, 1; 1, 0, 0]

theorem gl3Example_mul_inv : gl3Example * gl3ExampleInv = 1 := by
  unfold gl3Example gl3ExampleInv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem gl3ExampleInv_mul : gl3ExampleInv * gl3Example = 1 := by
  unfold gl3Example gl3ExampleInv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]




/-- The rank-three example as an element of the monodromy group `GL₃(ℤ)`. -/
def gl3Unit : IntGL 3 where
  val := gl3Example
  inv := gl3ExampleInv
  val_inv := gl3Example_mul_inv
  inv_val := gl3ExampleInv_mul


end Rank3


end Novelty.MirrorBridge


