-- Prove2me | Theorems.Thm_ClassGroupResidueDial_unit_cast_of_isCoprime
-- name    : ClassGroupResidueDial.unit_cast_of_isCoprime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:29:10.084191+00:00
-- url     : https://prove2.me/theorems/6e6f895b-7a4a-4d59-b1ab-bbff95d9d267
-- title:
--   Cast an integer coprime to `m` to a unit of `ZMod m`.
-- statement:
--   Cast an integer coprime to `m` to a unit of `ZMod m`.
--
--   ```lean
--   theorem ClassGroupResidueDial.unit_cast_of_isCoprime{N : ℤ} (h : IsCoprime N (m : ℤ)) :
--       ∃ u : ZMod m, u * (N : ZMod m) = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ClassGroupResidueDial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ClassGroupResidueDial.lean#L68

-- Thm stub generated from Algebra/ClassGroupResidueDial.lean
import Mathlib
import Definitions.Def_Algebra_ClassGroupResidueDial
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

open ClassGroupResidueDial

/-! ## 1. Abstract residue dials -/


variable {m : ℕ} {ι : Type*}

theorem ClassGroupResidueDial.unit_cast_of_isCoprime{N : ℤ} (h : IsCoprime N (m : ℤ)) :
    ∃ u : ZMod m, u * (N : ZMod m) = 1 := by sorry
