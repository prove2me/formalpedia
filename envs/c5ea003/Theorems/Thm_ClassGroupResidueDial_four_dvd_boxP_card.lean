-- Prove2me | Theorems.Thm_ClassGroupResidueDial_four_dvd_boxP_card
-- name    : ClassGroupResidueDial.four_dvd_boxP_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:28:58.008231+00:00
-- url     : https://prove2.me/theorems/835f1547-3049-49ea-a5f3-a18d21e1f286
-- title:
--   The unit action is free.
-- statement:
--   **The unit action is free.**  If `N` is coprime to `20` and is not a perfect
--   square, then no representation `N = x² + 5y²` has `x = 0` or `y = 0`, so the four
--   sign changes `(±x, ±y)` are distinct: the number of representations is divisible
--   by `4`.  (This is the `4` in the observed `8 = 4 · 2`: two ideal factorisations,
--   four units.)
--
--   ```lean
--   theorem ClassGroupResidueDial.four_dvd_boxP_card{N : ℤ} (hN : IsCoprime N 20) (hsq : ∀ k : ℤ, k ^ 2 ≠ N)
--       (Bx By : ℤ) : 4 ∣ (boxP N Bx By).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/ClassGroupResidueDial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/ClassGroupResidueDial.lean#L435

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






/-! ## 2. The discriminant `-20` dial -/










/-! ## 3. Consequences for `D = -20`: exclusivity and the dial -/






/-! ## 4. Gauss composition: the class group is `ℤ/2` -/





/-! ## 5. The refutation: PP and NN semiprimes are indistinguishable -/









/-! ## 6. Why the collision is unavoidable: the dial is a quadratic character -/







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

theorem ClassGroupResidueDial.four_dvd_boxP_card{N : ℤ} (hN : IsCoprime N 20) (hsq : ∀ k : ℤ, k ^ 2 ≠ N)
    (Bx By : ℤ) : 4 ∣ (boxP N Bx By).card := by sorry
