-- Prove2me | Definitions.Def_mme_stothers_general_outer_profile
-- name    : mme_stothers_general_outer_profile
-- status  : Definition
-- author  : @allychan327
-- created : 2026-09-08T05:03:32.381064+00:00
-- url     : https://prove2.me/theorems/a8657d45-a5fe-4f5f-887d-a4a15197f0b3
-- title:
--   General integral outer-profile data
-- statement:
--   **Outer-profile data at an arbitrary integral ten-class profile.**
--
--   The published outer data for the Davie--Stothers fourth-power witness is stated at one fixed
--   rational profile, the exact stationary witness with denominator $97{,}942{,}072$. These
--   definitions are the same data with the profile as a parameter.
--
--   An *integral ten-class profile* is a vector $\beta:\{1,\dots,10\}\to\mathbb N$ of class counts.
--   Writing $n_i$ for the Table-1 multiplicities, its weighted total is $D=\sum_i n_i\beta_i$, the
--   associated normalized profile is $a_i=\beta_i/D$ (a point of $Z$ when $\beta$ is strictly
--   positive), and its nine-grade marginal numerators are $M_j=(Q\beta)_j$, obtained by applying the
--   integer coefficient matrix of Equation (5.2) to the unnormalized $\beta$. At scale $m$ the outer
--   addresses have length $N=3Dm$ and the exact class counts are $\beta_i m$.
--
--   On top of these the file records, all parameterized by $\beta$: outer addresses and their joint
--   types, the exact-profile and marginally-regular address subtypes, coordinatewise support
--   ($i+j+k=8$), the marginal-supported ambient hypergraph, mixed addresses and the induced /
--   mode-disjoint conditions, vertex closure for deterministic collision pruning, exact target edges
--   and target--ambient collisions, and finally the $45$-cell joint histogram together with the star
--   degree $\prod_j M_jm!\,/\,\prod_\sigma (\text{joint count})!$ counting completions of one fixed
--   mode word.
--
--   There are no extraction or cardinality claims here; this is interface data only. Taking
--   $\beta=(98,1862,73075,1023050,3626000,98000,2156000,13720000,21560000,38710000)$ recovers the
--   published fixed witness, with $D=97{,}942{,}072$ and $M=(5822170,31951724,86288150,106906100,
--   56252000,6358100,244150,3724,98)$ exactly.
--
--   **Formalization note.** Names are prefixed `gen` so that nothing collides with the existing
--   `fixed*` data, and the same explicit six-permutation presentation of the orbit relation is used
--   so that class membership stays decidable.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3 and Section 5, Equations (5.2)-(5.3); https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fourth_data
import Mathlib.Data.Finset.Prod

open MME BigOperators

namespace MME.StothersFourth

set_option autoImplicit false

/-!
# Outer-profile data at an arbitrary integral ten-class profile

This is the profile-parametric form of the exact outer data used by the fixed
Davie--Stothers witness.  Every definition below is the literal `fixed*`
definition with the two hard-coded integer vectors replaced by a parameter
`base : Fin 10 → ℕ` and its derived marginal counts.  There are no extraction
or cardinality claims here.
-/

/-- Weighted total of an integral ten-class profile: `D = ∑_r n_r β_r`.
This is the common denominator of the normalized profile. -/
def genProfileScale (base : Fin 10 → ℕ) : ℕ :=
  ∑ r : Fin 10, classMultiplicity r * base r

/-- One period of class counts at scale `m`. -/
def genProfileCount (base : Fin 10 → ℕ) (m : ℕ) (i : Fin 10) : ℕ :=
  base i * m

/-- The normalized profile `a = β / D`, a point of `Z` when `β` is positive. -/
noncomputable def genProfileB (base : Fin 10 → ℕ) : Fin 10 → ℝ :=
  fun i ↦ (base i : ℝ) / (genProfileScale base : ℝ)

/-- A decidable presentation of the six permutations of three coordinates. -/
def genSameOrbitExplicit (sigma rho : Fin 3 → Fin 9) : Prop :=
  (sigma 0 = rho 0 ∧ sigma 1 = rho 1 ∧ sigma 2 = rho 2) ∨
  (sigma 0 = rho 0 ∧ sigma 1 = rho 2 ∧ sigma 2 = rho 1) ∨
  (sigma 0 = rho 1 ∧ sigma 1 = rho 0 ∧ sigma 2 = rho 2) ∨
  (sigma 0 = rho 1 ∧ sigma 1 = rho 2 ∧ sigma 2 = rho 0) ∨
  (sigma 0 = rho 2 ∧ sigma 1 = rho 0 ∧ sigma 2 = rho 1) ∨
  (sigma 0 = rho 2 ∧ sigma 1 = rho 1 ∧ sigma 2 = rho 0)

instance genDecidableSameOrbitExplicit (sigma rho : Fin 3 → Fin 9) :
    Decidable (genSameOrbitExplicit sigma rho) := by
  unfold genSameOrbitExplicit
  infer_instance

/-- The `3Dm` positions at scale `m`. -/
def genOuterLength (base : Fin 10 → ℕ) (m : ℕ) : ℕ :=
  3 * (genProfileScale base * m)

def GenOuterAddress (base : Fin 10 → ℕ) (m : ℕ) : Type :=
  Fin 3 → Fin (genOuterLength base m) → Fin 9

def genAddressType {base : Fin 10 → ℕ} {m : ℕ} (a : GenOuterAddress base m)
    (k : Fin (genOuterLength base m)) : Fin 3 → Fin 9 :=
  fun s ↦ a s k

def genClassOrbit (r : Fin 10) : Finset (Fin 3 → Fin 9) :=
  Finset.univ.filter (fun sigma ↦ genSameOrbitExplicit sigma (classRep r))

/-- Transpose of the integer coefficient matrix in Equation (5.2): row `r` is
the nine-grade marginal contribution of one member of class `r`. -/
def genClassMarginalMultiplicity : Fin 10 → Fin 9 → ℕ :=
  ![![2, 0, 0, 0, 0, 0, 0, 0, 1],
    ![2, 2, 0, 0, 0, 0, 0, 2, 0],
    ![2, 0, 2, 0, 0, 0, 2, 0, 0],
    ![2, 0, 0, 2, 0, 2, 0, 0, 0],
    ![1, 0, 0, 0, 2, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 1, 0, 0],
    ![0, 2, 2, 0, 0, 2, 0, 0, 0],
    ![0, 2, 0, 2, 2, 0, 0, 0, 0],
    ![0, 0, 2, 0, 1, 0, 0, 0, 0],
    ![0, 0, 1, 2, 0, 0, 0, 0, 0]]

/-- Numerators of the nine-grade marginal of `base`, i.e. `(Q β)_j`. -/
def genMarginalBaseCount (base : Fin 10 → ℕ) (j : Fin 9) : ℕ :=
  ∑ r : Fin 10, genClassMarginalMultiplicity r j * base r

def genMarginalCount (base : Fin 10 → ℕ) (m : ℕ) (j : Fin 9) : ℕ :=
  genMarginalBaseCount base j * m

/-- Every member of class `r` occurs this many times; unsupported joint types
have multiplicity zero. -/
def genJointMultiplicity (base : Fin 10 → ℕ) (m : ℕ)
    (sigma : Fin 3 → Fin 9) : ℕ :=
  ∑ r : Fin 10,
    if genSameOrbitExplicit sigma (classRep r) then
      genProfileCount base m r
    else 0

def GenExactOuterAddress (base : Fin 10 → ℕ) (m : ℕ) : Type :=
  {a : GenOuterAddress base m //
    ∀ sigma : Fin 3 → Fin 9,
      (Finset.univ.filter (fun k ↦ genAddressType a k = sigma)).card =
        genJointMultiplicity base m sigma}

def GenMarginallyRegular {base : Fin 10 → ℕ} {m : ℕ}
    (a : GenOuterAddress base m) : Prop :=
  ∀ s : Fin 3, ∀ j : Fin 9,
    (Finset.univ.filter (fun k ↦ a s k = j)).card = genMarginalCount base m j

def GenCoordinatewiseSupported {base : Fin 10 → ℕ} {m : ℕ}
    (a : GenOuterAddress base m) : Prop :=
  ∀ k, (∑ s, ((a s k).val : ℕ)) = 8

/-- Full marginal-supported ambient hypergraph for the outer hash. -/
def GenMarginalSupportedAddress (base : Fin 10 → ℕ) (m : ℕ) : Type :=
  {a : GenOuterAddress base m //
    GenCoordinatewiseSupported a ∧ GenMarginallyRegular a}

def GenHasExactJointProfile {base : Fin 10 → ℕ} {m : ℕ}
    (a : GenMarginalSupportedAddress base m) : Prop :=
  ∀ sigma : Fin 3 → Fin 9,
    (Finset.univ.filter (fun k ↦ genAddressType a.1 k = sigma)).card =
      genJointMultiplicity base m sigma

def genMixedAddress {base : Fin 10 → ℕ} {m : ℕ}
    (x y z : GenOuterAddress base m) : GenOuterAddress base m
  | ⟨0, _⟩ => x 0
  | ⟨1, _⟩ => y 1
  | ⟨2, _⟩ => z 2
  | ⟨_ + 3, h⟩ => absurd h (by omega)

def GenModeDisjoint {base : Fin 10 → ℕ} {m : ℕ}
    (F : Finset (GenExactOuterAddress base m)) : Prop :=
  ∀ x : F, ∀ y : F, x ≠ y → ∀ s : Fin 3, x.1.1 s ≠ y.1.1 s

def GenInduced {base : Fin 10 → ℕ} {m : ℕ}
    (F : Finset (GenExactOuterAddress base m)) : Prop :=
  ∀ x : F, ∀ y : F, ∀ z : F,
    GenCoordinatewiseSupported (genMixedAddress x.1.1 y.1.1 z.1.1) →
      x = y ∧ y = z

def GenInducedModeDisjoint {base : Fin 10 → ℕ} {m : ℕ}
    (F : Finset (GenExactOuterAddress base m)) : Prop :=
  GenModeDisjoint F ∧ GenInduced F

/-- Closure condition needed by deterministic collision pruning. -/
def GenMarginalVertexClosed {base : Fin 10 → ℕ} {m : ℕ}
    (E : Finset (GenMarginalSupportedAddress base m)) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, ∀ z ∈ E,
    GenCoordinatewiseSupported (genMixedAddress x.1 y.1 z.1) →
      ∃ e ∈ E, e.1 = genMixedAddress x.1 y.1 z.1

/-- Exact-profile target edges inside a marginal-supported ambient family. -/
noncomputable def genExactTargetEdges {base : Fin 10 → ℕ} {m : ℕ}
    (E : Finset (GenMarginalSupportedAddress base m)) :
    Finset (GenMarginalSupportedAddress base m) := by
  classical
  exact E.filter GenHasExactJointProfile

/-- Ordered target--ambient pairs sharing at least one mode word. -/
noncomputable def genTargetAmbientCollisions {base : Fin 10 → ℕ} {m : ℕ}
    (E : Finset (GenMarginalSupportedAddress base m)) :
    Finset (GenMarginalSupportedAddress base m ×
      GenMarginalSupportedAddress base m) := by
  classical
  exact (genExactTargetEdges E ×ˢ E).filter (fun p ↦
    p.1 ≠ p.2 ∧ ∃ s : Fin 3, p.1.1 s = p.2.1 s)

/-! ### The 45-cell joint histogram -/

/-- The 45 ordered joint types in the support of the fourth-power grading. -/
abbrev GenHashSupportTriple :=
  {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}

abbrev GenHashJointMultiplicityTable := GenHashSupportTriple → ℕ

def genHashSupportedTypeAt {base : Fin 10 → ℕ} {m : ℕ}
    (a : GenMarginalSupportedAddress base m)
    (k : Fin (genOuterLength base m)) : GenHashSupportTriple :=
  ⟨genAddressType a.1 k, by
    simpa only [genAddressType] using a.2.1 k⟩

/-- The ordered 45-cell joint histogram of a marginally regular address. -/
def genHashJointTable {base : Fin 10 → ℕ} {m : ℕ}
    (a : GenMarginalSupportedAddress base m) :
    GenHashJointMultiplicityTable :=
  fun sigma ↦ Fintype.card
    {k : Fin (genOuterLength base m) // genHashSupportedTypeAt a k = sigma}

/-- The exact target histogram, restricted to the 45 supported cells. -/
def genHashTargetJointTable (base : Fin 10 → ℕ) (m : ℕ)
    (sigma : GenHashSupportTriple) : ℕ :=
  genJointMultiplicity base m sigma.1

/-- Number of completions of one mode word with the exact target table. -/
def genHashTargetStarDegree (base : Fin 10 → ℕ) (m : ℕ) : ℕ :=
  (∏ j : Fin 9, (genMarginalCount base m j).factorial) /
    ∏ sigma : GenHashSupportTriple,
      (genHashTargetJointTable base m sigma).factorial

end MME.StothersFourth


