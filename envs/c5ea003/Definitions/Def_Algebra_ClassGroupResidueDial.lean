-- Prove2me | Definitions.Def_Algebra_ClassGroupResidueDial
-- name    : Algebra_ClassGroupResidueDial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:09:14.928353+00:00
-- url     : https://prove2.me/theorems/a218d53b-f333-45ea-9e2f-eb7254a1139e
-- title:
--   Aether Catalog definitions — Algebra_ClassGroupResidueDial
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.ClassGroupResidueDial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/ClassGroupResidueDial.lean by skeleton subtraction
import Mathlib
/-
# The Extrinsic Class-Group Representation Vector is a Residue Dial

Formal core of the *factor3* investigation
`ResearchOutput/NewMathematics/35_ClassGroup_ResidueDial.md`
(experiment RANDOM-BQF #370).

## The question

Attach to an integer `N` an *extrinsic* discriminant `D` (independent of `N`),
form the finitely many reduced binary quadratic forms `Q_1, … , Q_h` of
discriminant `D`, and record the **representation vector**

  `r(N) = ( #{(x,y) : Q_1(x,y) = N}, … , #{(x,y) : Q_h(x,y) = N} )`.

Computing this vector is cheap (`poly(|D|, log N)`, no factoring).  The hope of
the round-13 brainstorm was that the individual entries feel the *separate*
Legendre symbols `(D/p)`, `(D/q)` of the factors of `N = p q`, so that the
vector could distinguish factorisation *types* which have the same residue
`N mod |D|`.

## What is proved here (`D = -20`, `h = 2`)

The two reduced forms of discriminant `-20` are

  `P(x,y) = x² + 5y²`   and   `Q(x,y) = 2x² + 2xy + 3y²`.

* `ClassGroupResidueDial.sound20` : a value of `P` coprime to `20` is `≡ 1, 9 (mod 20)`;
  a value of `Q` coprime to `20` is `≡ 3, 7 (mod 20)`  (finite check in `ZMod 20`).
* `ClassGroupResidueDial.ResidueDial.readout_eq` : consequently the *index of the class that
  represents `N`* is a **function of `N mod 20` alone** — the "residue dial".
* `ClassGroupResidueDial.comp20` : Gauss composition, realised by explicit bilinear
  identities: the two classes form the group `ℤ/2` under multiplication of
  represented integers (`P·P = P`, `Q·Q = P`, `P·Q = Q`).
* `ClassGroupResidueDial.obs_pp_eq_obs_nn` : **the refutation.**  If `p, q` are both
  represented by the principal form and `p', q'` are both represented by the
  non-principal form, then `pq` and `p'q'` have *identical* observation vectors
  `(true, false)`.  The "PP" and "NN" factorisation types are invisible.
* Exact counts (`reps_21_ncard`, `reps_87_ncard`, `reps_1189_ncard`) confirm the
  numerical `(8,0)` signature of the experiment on both a PP and an NN semiprime.

The abstract notion `ResidueDial` isolates exactly what makes the collapse
happen: *soundness* (each class only represents certain residues) plus
*disjointness* of those residue sets.  Any such family is factor-blind.
-/

namespace ClassGroupResidueDial

/-! ## 1. Abstract residue dials -/

/-- A **residue dial** modulo `m` with class index type `ι`: a family of
"is represented by class `i`" predicates on `ℤ`, together with pairwise disjoint
sets of residues mod `m` that *contain* all the unit values of each class.

The only inputs are `sound` and `disj`; everything in §1 is a consequence. -/
structure ResidueDial (m : ℕ) (ι : Type*) where
  /-- `repr i N` : the integer `N` is represented by the `i`-th class. -/
  repr : ι → ℤ → Prop
  /-- The residues mod `m` allowed for the `i`-th class. -/
  res : ι → Finset (ZMod m)
  /-- Soundness: a unit value of class `i` lands in `res i`. -/
  sound : ∀ i (N : ℤ), (∃ u : ZMod m, u * (N : ZMod m) = 1) → repr i N → ((N : ZMod m) ∈ res i)
  /-- The residue sets of distinct classes are disjoint. -/
  disj : ∀ i j, i ≠ j → ∀ a, a ∈ res i → a ∉ res j

variable {m : ℕ} {ι : Type*}




open Classical in
/-- The **dial**: the explicit function `ZMod m → ι` that the observation
factors through. -/
noncomputable def ResidueDial.readout [Inhabited ι] (d : ResidueDial m ι) (a : ZMod m) : ι :=
  if h : ∃ i, a ∈ d.res i then h.choose else default


/-! ## 2. The discriminant `-20` dial -/

/-- Represented by the principal form `x² + 5y²` of discriminant `-20`. -/
def ReprP (N : ℤ) : Prop := ∃ x y : ℤ, x ^ 2 + 5 * y ^ 2 = N

/-- Represented by the non-principal form `2x² + 2xy + 3y²` of discriminant `-20`. -/
def ReprQ (N : ℤ) : Prop := ∃ x y : ℤ, 2 * x ^ 2 + 2 * x * y + 3 * y ^ 2 = N

/-- The two-element family of reduced forms of discriminant `-20`,
indexed by `Bool` (`false` = principal class, `true` = non-principal class). -/
def repr20 : Bool → ℤ → Prop
  | false => ReprP
  | true => ReprQ

/-- The genus characters mod `20`: the principal class only represents `1, 9`,
the other class only `3, 7`. -/
def res20 : Bool → Finset (ZMod 20)
  | false => {1, 9}
  | true => {3, 7}

/-- Finite check in `ZMod 20`: every unit value of `x² + 5y²` is `1` or `9`. -/
theorem key20P : ∀ a b u : ZMod 20, u * (a ^ 2 + 5 * b ^ 2) = 1 →
    (a ^ 2 + 5 * b ^ 2) ∈ ({1, 9} : Finset (ZMod 20)) := by decide

/-- Finite check in `ZMod 20`: every unit value of `2x² + 2xy + 3y²` is `3` or `7`. -/
theorem key20Q : ∀ a b u : ZMod 20, u * (2 * a ^ 2 + 2 * a * b + 3 * b ^ 2) = 1 →
    (2 * a ^ 2 + 2 * a * b + 3 * b ^ 2) ∈ ({3, 7} : Finset (ZMod 20)) := by decide

theorem sound20 : ∀ (i : Bool) (N : ℤ), (∃ u : ZMod 20, u * (N : ZMod 20) = 1) →
    repr20 i N → ((N : ZMod 20) ∈ res20 i) := by
  rintro (_ | _) N ⟨u, hu⟩ ⟨x, y, rfl⟩
  · have h : ((x ^ 2 + 5 * y ^ 2 : ℤ) : ZMod 20) = (x : ZMod 20) ^ 2 + 5 * (y : ZMod 20) ^ 2 := by
      push_cast; ring
    rw [h] at hu ⊢
    exact key20P _ _ _ hu
  · have h : ((2 * x ^ 2 + 2 * x * y + 3 * y ^ 2 : ℤ) : ZMod 20)
        = 2 * (x : ZMod 20) ^ 2 + 2 * (x : ZMod 20) * (y : ZMod 20) + 3 * (y : ZMod 20) ^ 2 := by
      push_cast; ring
    rw [h] at hu ⊢
    exact key20Q _ _ _ hu

theorem disj20 : ∀ i j : Bool, i ≠ j → ∀ a : ZMod 20, a ∈ res20 i → a ∉ res20 j := by decide

/-- The discriminant `-20` residue dial. -/
def dial20 : ResidueDial 20 Bool where
  repr := repr20
  res := res20
  sound := sound20
  disj := disj20

/-! ## 3. Consequences for `D = -20`: exclusivity and the dial -/






/-! ## 4. Gauss composition: the class group is `ℤ/2` -/





/-! ## 5. The refutation: PP and NN semiprimes are indistinguishable -/

open Classical in
/-- The observation available to a would-be factoring algorithm: which reduced
forms of discriminant `-20` represent `N`. -/
noncomputable def obs (N : ℤ) : Bool × Bool := (decide (ReprP N), decide (ReprQ N))








/-! ## 6. Why the collision is unavoidable: the dial is a quadratic character -/

/-- The four residues mod `20` that occur at all (`(D/N) = 1`). -/
def D20 : Finset (ZMod 20) := {1, 3, 7, 9}

/-- The dial bit: `false` = principal class, `true` = non-principal class. -/
def dialBit (a : ZMod 20) : Bool := !(a = 1 || a = 9)





/-! ## 7. Lab notes: exact representation counts

The experiment reported the signature `(8, 0)` for semiprimes `N ≡ 1, 9 (mod 20)`
whose prime factors are split, *independently of the PP/NN type*.  Here are three
certified instances:

| `N`    | factorisation | type | `r_P(N)` | `r_Q(N)` |
|--------|---------------|------|----------|----------|
| `21`   | `3 · 7`       | NN   | `8`      | `0`      |
| `1189` | `29 · 41`     | PP   | `8`      | `0`      |
| `87`   | `3 · 29`      | PN   | `0`      | `8`      |
-/

/-- All representations of `N` by `x² + 5y²` inside an explicit box. -/
noncomputable def boxP (N Bx By : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-Bx) Bx) ×ˢ (Finset.Icc (-By) By)).filter (fun p => p.1 ^ 2 + 5 * p.2 ^ 2 = N)

/-- All representations of `N` by `2x² + 2xy + 3y²` inside an explicit box. -/
noncomputable def boxQ (N Bx By : ℤ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-Bx) Bx) ×ˢ (Finset.Icc (-By) By)).filter
    (fun p => 2 * p.1 ^ 2 + 2 * p.1 * p.2 + 3 * p.2 ^ 2 = N)











end ClassGroupResidueDial


