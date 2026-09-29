-- Prove2me | Definitions.Def_Applications_PfaffianGiambelli_Pfaffian
-- name    : Applications_PfaffianGiambelli_Pfaffian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:21.593034+00:00
-- url     : https://prove2.me/theorems/3c46bd0c-ef12-4c3f-8b9b-ca78dc0a8d08
-- title:
--   Aether Catalog definitions — Applications_PfaffianGiambelli_Pfaffian
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PfaffianGiambelli.Pfaffian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PfaffianGiambelli/Pfaffian.lean by skeleton subtraction
import Mathlib

/-!
# Pfaffians of small skew-symmetric matrices and the Giambelli backbone

This file develops the elementary linear algebra that underlies the **Pfaffian
Giambelli formula** for (shifted, `t`-deformed) Schur `Q`-functions.  The classical
formula expresses a Schur `Q`-function indexed by a strict partition as a *Pfaffian*
of two-row Schur `Q`-functions, and its `t`-deformation (the shifted `t`-Schur
functions of the Greaves–Jing–Zhu construction) has exactly the same shape.

The *algebraic engine* of every such formula is the Pfaffian itself, so here we
isolate and fully prove the structural facts that make the engine run, for the
two smallest non-trivial sizes `k = 1` (a `2 × 2` block) and `k = 2` (a `4 × 4`
block, the first genuinely interesting Pfaffian):

* `Matrix.det_fin_four` — the explicit Laplace expansion of a `4 × 4` determinant
  (not in Mathlib at this version; proved here once and reused);
* `pf2_sq_eq_det`, `pf4_sq_eq_det` — the defining property **`Pf(A)² = det A`** for
  alternating matrices, the identity that pins the Pfaffian down up to sign;
* `pf4_swap12_neg` — the **alternating / sign law**: a transposition of two indices
  flips the sign of the Pfaffian, mirroring the Clifford anticommutation of the
  odd Greaves–Jing–Zhu operators;
* `pf4_giambelli` — the **complementary-minor (Giambelli) expansion** writing the
  `4 × 4` Pfaffian as an alternating sum of products of `2 × 2` Pfaffians; this is
  the `k = 2` instance of the recursive Pfaffian Giambelli formula.

Nothing here is definitional fluff: `pf4_sq_eq_det` is a genuine degree-`4`
polynomial identity in the `12` independent entries, and is what forces the
Pfaffian to be *the* square root of the determinant.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): for an alternating `2k × 2k` matrix there is a
  polynomial `Pf` with `Pf² = det`, and `Pf` of a `4 × 4` block expands over
  complementary index pairs with signs `+ - +`, exactly like a Schur `Q` Giambelli
  Pfaffian.
* Experiment (Experimenter): defined `pf2`, `pf4` by their matching expansions and
  attacked `Pf² = det`.  The `4 × 4` determinant is not available in Mathlib
  (`det_fin_four` is missing), so we first reduce `det` via `det_succ_row_zero`
  and `det_fin_three`, evaluating the residual `Fin.succAbove` indices by `rfl`,
  then close the polynomial identity by `ring` after substituting the alternating
  relations.
* Analysis (Analyst): `Pf² = det` is *true but hard for `simp` alone* — it needs the
  hand-built `det_fin_four` plus `ring`; this is why the result is non-trivial.
  The sign law `pf4_swap12_neg` needs only skewness (not the zero diagonal), while
  `Pf² = det` needs both, matching the fact that "alternating" is strictly stronger
  than "skew" outside fields of characteristic `≠ 2`.
* Critique (Critic): `pf4_giambelli` is a reorganisation provable by `simp`, so it is
  recorded as a structural corollary, *not* as a headline theorem; the headline
  theorems (`pf2_sq_eq_det`, `pf4_sq_eq_det`, `pf4_swap12_neg`) each use `ring`
  on top of a non-trivial rewrite and hold over an arbitrary commutative ring.
* Synthesis (PI): this file is the reusable Pfaffian core; `ShiftedTSchur.lean`
  feeds it `t`-deformed alternating matrices to obtain the shifted `t`-Schur
  Pfaffian Giambelli statements.
-/

open Matrix Finset

namespace PfaffianGiambelli

variable {R : Type*} [CommRing R]

/-- Pfaffian of a `2 × 2` matrix (the `k = 1` case): the single super-diagonal
entry.  For an alternating matrix this is the unique square root of the
determinant. -/
def pf2 (A : Matrix (Fin 2) (Fin 2) R) : R := A 0 1

/-- Pfaffian of a `4 × 4` matrix (the `k = 2` case): the signed sum over the three
perfect matchings of `{0,1,2,3}`.  This is the first genuinely interesting
Pfaffian and the `k = 2` instance of the Pfaffian Giambelli formula. -/
def pf4 (A : Matrix (Fin 4) (Fin 4) R) : R :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2






end PfaffianGiambelli


