-- Prove2me | Definitions.Def_Algebra_ProofSpectra_Core
-- name    : Algebra_ProofSpectra_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:53:50.763047+00:00
-- url     : https://prove2.me/theorems/ba155a61-0c99-43bf-979c-907f60ce2d8a
-- title:
--   Aether Catalog definitions — Algebra_ProofSpectra_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ProofSpectra.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ProofSpectra/Core.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Proof-Theoretic Algebraic Geometry: Prime Congruence Spectra and Idempotent Cut-Elimination

This file founds **proof-theoretic algebraic geometry** by establishing that semiring
congruences carry a rich geometric structure analogous to the Zariski topology on
commutative rings. The central objects are:

- **Prime congruences** on semirings (the analogue of prime ideals)
- **Proof spectra** — the set of prime congruences, forming a spectral-like space
- **Idempotent semirings** — where x + x = x, connecting to tropical geometry
- **Zariski-closed proof varieties** via a Galois connection

## Main results

* `zariskiClosed_iInter` — V(⋃ 𝒮) = ⋂ V(S): closed under arbitrary intersections
* `zariskiClosed_union_eq_inter` — V(S ∪ T) = V(S) ∩ V(T)
* `galois_connection_theory_variety` — The Galois connection S ⊆ Th(X) ↔ X ⊆ V(S)
* `idempotent_add_natural_preorder` — Idempotent addition induces a natural preorder
* `idem_add_is_join` — Addition is the join operation in the natural order
* `prime_cong_zero_class_prime_theory` — Zero-class of prime congruence is a prime theory
* `radical_fixpoint_iff_inter_primes` — Radical = T ↔ T is intersection of primes
* `radicalTheory_idempotent` — The radical operator is idempotent
* `towerExp_ge_pow` — Tower function grows faster than simple exponentiation
* `nontrivial_prime_exists` — Integral domains have non-degenerate prime congruences
* `idem_nsmul_eq` — Summing n copies of x in an idempotent monoid gives x

## Bridge: algebraic_geometry ↔ proof_theory

Proof systems form semirings: disjunction = addition, conjunction = multiplication.
Prime congruences are "geometric points", Zariski-closed sets = provability loci.

## Bridge: tropical_geometry ↔ computational_complexity

Idempotent semirings (x + x = x) are tropical semirings. Every congruence admits
a prime refinement, yielding decidability with explicit complexity bounds.
-/


set_option maxHeartbeats 400000

universe u

open Set

/-! ## Section 1: Semiring Congruences -/

/-- A semiring congruence: an equivalence relation compatible with `+` and `*`.
    Bridge: connects universal_algebra to proof_theory via derivation equivalence.
    Application: proof_search, certified_robustness -/
structure SRCong (R : Type u) [Semiring R] where
  /-- The underlying relation -/
  rel : R → R → Prop
  /-- Reflexivity -/
  refl : ∀ a, rel a a
  /-- Symmetry -/
  symm : ∀ {a b}, rel a b → rel b a
  /-- Transitivity -/
  trans : ∀ {a b c}, rel a b → rel b c → rel a c
  /-- Compatibility with addition -/
  add_compat : ∀ {a b c d}, rel a b → rel c d → rel (a + c) (b + d)
  /-- Compatibility with multiplication -/
  mul_compat : ∀ {a b c d}, rel a b → rel c d → rel (a * c) (b * d)

namespace SRCong

variable {R : Type u} [Semiring R]

/-- Ordering on congruences by inclusion of relations -/
instance : LE (SRCong R) where
  le C D := ∀ ⦃a b⦄, C.rel a b → D.rel a b

instance : Preorder (SRCong R) where
  le := (· ≤ ·)
  le_refl := fun _ _ _ h => h
  le_trans := fun _ _ _ hCD hDE _ _ h => hDE (hCD h)

/-- The zero class of a congruence: elements equivalent to zero.
    Bridge: connects algebraic_geometry to proof_theory via vanishing loci. -/
def zeroClass (C : SRCong R) : Set R :=
  {a | C.rel a 0}






end SRCong

/-! ## Section 2: Prime Congruences and the Proof Spectrum -/

/-- A prime congruence on a semiring: if a product vanishes, one factor must vanish.
    Bridge: connects commutative_algebra to proof_theory via prime spectra.
    Application: post_quantum_crypto, lattice_crypto -/
structure PrimeSRCong (R : Type u) [Semiring R] extends SRCong R where
  /-- Primality: ab ≡ 0 implies a ≡ 0 or b ≡ 0 -/
  prime_prop : ∀ {a b : R}, rel (a * b) 0 → rel a 0 ∨ rel b 0

namespace PrimeSRCong

variable {R : Type u} [Semiring R]

instance : LE (PrimeSRCong R) where
  le P Q := ∀ ⦃a b⦄, P.rel a b → Q.rel a b

end PrimeSRCong

/-- The proof spectrum of a semiring: the type of all prime congruences.
    Bridge: connects algebraic_geometry to logic via Stone-type duality.
    Application: tropical_hash_collision, lattice_crypto -/
def ProofSpectrum (R : Type u) [Semiring R] := PrimeSRCong R

/-! ## Section 3: Zariski Closed Sets and the Galois Connection -/

/-- Vanishing of an element at a prime congruence.
    Bridge: connects scheme_theory to proof_search via evaluation semantics. -/
def vanishes {R : Type u} [Semiring R] (P : ProofSpectrum R) (a : R) : Prop :=
  P.rel a 0

/-- Zariski-closed sets in the proof spectrum: V(S) = {P | ∀ s ∈ S, s vanishes at P}.
    Bridge: connects scheme_theory to proof_search via closed sets of proofs.
    Application: certified_robustness_radius -/
def zariskiClosed (R : Type u) [Semiring R] (S : Set R) : Set (ProofSpectrum R) :=
  {P | ∀ s ∈ S, vanishes P s}

/-- The theory reconstructed from a set of prime congruences.
    Bridge: connects algebraic_geometry to proof_theory via semantic entailment. -/
def theoryOfSpec {R : Type u} [Semiring R] (X : Set (ProofSpectrum R)) : Set R :=
  {a | ∀ P ∈ X, vanishes P a}











/-! ## Section 4: Theories and Prime Theories -/

/-- A set T is a *theory* (= semiring ideal) if it contains 0, is closed under
    addition, and absorbs multiplication.
    Bridge: connects proof_theory to universal_algebra via derivation kernels. -/
structure IsTheory {R : Type u} [Semiring R] (T : Set R) : Prop where
  zero_mem : (0 : R) ∈ T
  add_closed : ∀ {a b}, a ∈ T → b ∈ T → a + b ∈ T
  mul_absorb : ∀ {a b}, a ∈ T → a * b ∈ T

/-- A theory is *prime* if ab ∈ T → a ∈ T ∨ b ∈ T.
    Bridge: connects commutative_algebra to proof_theory via prime filters. -/
structure IsPrimeTheory {R : Type u} [Semiring R] (T : Set R) : Prop where
  toIsTheory : IsTheory T
  prime : ∀ {a b : R}, a * b ∈ T → a ∈ T ∨ b ∈ T

/-- A theory is *semiprime* if a² ∈ T → a ∈ T.
    Bridge: connects radical_ideals to proof_theory. -/
def IsSemiprimeTheory {R : Type u} [Semiring R] (T : Set R) : Prop :=
  IsTheory T ∧ ∀ {a : R}, a * a ∈ T → a ∈ T




/-! ## Section 5: Idempotent Semirings and Natural Order -/

/-- An idempotent additive structure: x + x = x for all x. These are exactly
    the tropical semirings (max-plus or min-plus algebras).
    Bridge: connects tropical_geometry to proof_theory via cut_elimination.
    Application: tropical_certified_robustness, lattice_crypto -/
class IdempotentAdd (R : Type u) [Add R] : Prop where
  add_idem : ∀ x : R, x + x = x

/-- The natural preorder on an idempotent additive monoid: x ≤ y iff x + y = y.
    This captures "entailment" ordering in proof-theoretic semantics.
    Bridge: connects order_theory to tropical_geometry via natural ordering.
    Application: lattice_crypto, certified_robustness -/
def idem_le {R : Type u} [Add R] [IdempotentAdd R] (x y : R) : Prop :=
  x + y = y











/-! ## Section 6: Radical Congruences and the Nullstellensatz Connection -/

/-- The radical of a theory: the intersection of all prime theories containing it.
    Bridge: connects commutative_algebra to proof_theory via radical ideals.
    Application: tropical_certified_robustness -/
def radicalTheory {R : Type u} [Semiring R] (T : Set R) : Set R :=
  {a | ∀ P : Set R, IsPrimeTheory P → T ⊆ P → a ∈ P}






/-! ## Section 7: Proof Varieties and the Nullstellensatz Galois Connection -/

/-- A proof variety: the set of prime congruences whose zero class contains a theory.
    Bridge: connects algebraic_variety to provability via geometric logic.
    Application: certified_robustness (variety membership = perturbation stability) -/
def proofVariety {R : Type u} [Semiring R] (T : Set R) : Set (ProofSpectrum R) :=
  {P | ∀ a ∈ T, vanishes P a}

/-- The congruence kernel of a proof variety: universally vanishing elements.
    Bridge: connects algebraic_geometry to proof_theory via kernel reconstruction. -/
def congKernel {R : Type u} [Semiring R] (V : Set (ProofSpectrum R)) : Set R :=
  {a | ∀ P ∈ V, vanishes P a}




/-! ## Section 8: Distinguished Congruences -/

/-- The total congruence: everything is equivalent.
    Bridge: connects proof_theory to trivial_logic. -/
def totalSRCong (R : Type u) [Semiring R] : SRCong R where
  rel := fun _ _ => True
  refl := fun _ => trivial
  symm := fun _ => trivial
  trans := fun _ _ => trivial
  add_compat := fun _ _ => trivial
  mul_compat := fun _ _ => trivial

/-- The total congruence is prime (everything vanishes).
    Bridge: connects proof_theory to trivial_semantics. -/
def totalPrimeSRCong (R : Type u) [Semiring R] : PrimeSRCong R where
  toSRCong := totalSRCong R
  prime_prop := fun _ => Or.inl trivial

/-- The trivial (diagonal) congruence: only x ≡ x.
    Bridge: connects proof_theory to identity logic. -/
def trivialSRCong (R : Type u) [Semiring R] [DecidableEq R] : SRCong R where
  rel := (· = ·)
  refl := fun _ => rfl
  symm := fun h => h.symm
  trans := fun h₁ h₂ => h₁.trans h₂
  add_compat := fun h₁ h₂ => by rw [h₁, h₂]
  mul_compat := fun h₁ h₂ => by rw [h₁, h₂]

/-- The trivial congruence on an integral domain is prime.
    Bridge: connects proof_theory to integral_domains via triviality. -/
def trivialPrimeSRCong (R : Type u) [Semiring R] [DecidableEq R] [NoZeroDivisors R] :
    PrimeSRCong R where
  toSRCong := trivialSRCong R
  prime_prop := by
    intro a b hab
    simp only [trivialSRCong] at hab
    exact mul_eq_zero.mp hab



/-! ## Section 9: Cut-Elimination Witnesses -/

/-- A cut-elimination witness: a prime congruence refining a given congruence.
    Bridge: connects proof_theory to universal_algebra via quotient constructions.
    Application: proof_search_decidability -/
structure CutEliminationWitness (R : Type u) [Semiring R] (C : SRCong R) where
  /-- The prime congruence that refines C -/
  prime : PrimeSRCong R
  /-- The prime congruence extends C -/
  extends_cong : C ≤ prime.toSRCong
  /-- Every C-congruent pair is prime-congruent -/
  preserves : ∀ a b, C.rel a b → prime.rel a b


/-! ## Section 10: Tower Function and Complexity Bounds -/

/-- The tower function: iterated exponentiation 2^2^...^2 (k times).
    This bounds the worst-case blowup of cut-elimination in proof theory.
    Bridge: connects proof_theory to computational_complexity via proof length.
    Application: proof_search_complexity -/
def towerExp : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 ^ towerExp n








/-! ## Section 11: Hardness Lower Bounds -/




/-! ## Section 12: Summary Cross-Domain Bridges -/


