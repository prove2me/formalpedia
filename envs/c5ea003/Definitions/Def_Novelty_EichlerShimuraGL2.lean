-- Prove2me | Definitions.Def_Novelty_EichlerShimuraGL2
-- name    : Novelty_EichlerShimuraGL2
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:21:33.200822+00:00
-- url     : https://prove2.me/theorems/00663749-6432-4154-a878-f969d5256bee
-- title:
--   Aether Catalog definitions — Novelty_EichlerShimuraGL2
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EichlerShimuraGL2`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EichlerShimuraGL2.lean by skeleton subtraction
import Mathlib
/-
# Eichler–Shimura and the local Frobenius data for GL₂ over ℚ

This file formalizes the **arithmetic skeleton of the GL₂ Langlands correspondence over `ℚ`**:
the way a weight-`2` Hecke eigenform `f` produces, at each good prime `p`, a `2`-dimensional
local Frobenius datum.  The classical dictionary is:

* the Hecke eigenvalue `a_p = a` of `f` is the **trace** of `Frob_p`;
* the prime `p` (the value of the cyclotomic character) is the **determinant** of `Frob_p`;
* the **characteristic polynomial** of `Frob_p` is the *Hecke polynomial* `X² − a·X + p`;
* the **Euler factor** of the `L`-function at `p` is `(1 − a·X + p·X²)⁻¹`;
* `Frob_p` satisfies the **Eichler–Shimura congruence relation**
  `Frob_p² − a·Frob_p + p = 0`, the rank-2 Cayley–Hamilton identity. Geometrically this is
  the relation `T_p ≡ Frob + ⟨p⟩·Frob∨ (mod p)` on the reduction of the modular curve.

These statements are exactly the GL₂ analogues of the GL₁ (cyclotomic) data already in the
catalog (`Catalog.NumberTheory.GL1Correspondence`, `Catalog.NumberTheory.Langlands.HeckeFactorization`):
there the Frobenius datum is a single unit (a Dirichlet character value); here it is a `2 × 2`
matrix, and the new content is the *quadratic* relation tying trace, determinant and Frobenius.

Main results:

* `EichlerShimuraGL2.heckePoly` — the Hecke / Frobenius characteristic polynomial `X² − a·X + b`.
* `EichlerShimuraGL2.eichlerShimura` — the Eichler–Shimura congruence relation as the rank-2
  Cayley–Hamilton identity `M·M = (tr M)·M − (det M)·1`.
* `EichlerShimuraGL2.heckePoly_factor` — Vieta: `heckePoly a b = (X − α)(X − β)` for eigenvalues
  `α, β` with `α + β = a`, `αβ = b`.
* `EichlerShimuraGL2.eulerFactor_factor` — the local Euler factor factors as
  `1 − a·X + b·X² = (1 − α·X)(1 − β·X)`.
* `EichlerShimuraGL2.frobMatrix` — the companion matrix realizing a Frobenius with prescribed
  trace `a` and determinant `p`, together with `frobMatrix_trace`, `frobMatrix_det`, and the
  Eichler–Shimura relation `frobMatrix_eichlerShimura`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the GL(1) correspondence in the catalog packages the local datum
of a Hecke character as a single unit (trace = determinant).  The bold GL₂ jump is that the
local datum becomes a genuine `2 × 2` matrix, and the *one new equation* governing it — beyond
"trace = a_p, det = p" — is the Eichler–Shimura congruence `Frob² = a·Frob − p`.  Conjecture:
this is not an extra axiom but a *theorem*, namely rank-2 Cayley–Hamilton, hence provable
unconditionally and uniformly in any commutative ring of coefficients.

Experiment (Experimenter): we avoid the heavy `Matrix.charpoly` / `aeval_self_charpoly`
machinery and instead prove the identity entrywise via `fin_cases` + `Matrix.mul_apply`,
`Matrix.trace_fin_two`, `Matrix.det_fin_two` and `ring`.  The companion matrix `!![0,-p;1,a]`
is then checked to have trace `a`, determinant `p`, and to satisfy the relation by specialization.
Vieta and the Euler-factor factorization are pure `ring` identities after `C_add`/`C_mul`.

Analysis (Analyst): the relation `M² = (tr M)M − (det M)·1` is the precise finite shadow of
"`Frob_p` has characteristic polynomial `X² − a_p X + p`"; it holds for *every* `2 × 2` matrix,
so the arithmetic input of Eichler–Shimura is the *identification* of `tr` with `a_p` and `det`
with `p`, not the algebraic relation itself.  The companion matrix shows the datum is realizable:
for any `(a, p)` there is a concrete Frobenius with that trace and determinant.

Critique (Critic): is `eichlerShimura` trivial?  No — it is the rank-2 Cayley–Hamilton theorem,
proved by an honest entrywise computation, not `rfl`/`decide`.  Is the companion matrix a wrapper?
No — it supplies the *existence* half (realizability of arbitrary local data) and feeds the
Deligne-bound file, where its eigenvalues are shown to be Weil numbers.  Corner cases: the
identities hold over any `CommRing`, including characteristic `p` (where Eichler–Shimura is
usually stated), so nothing is lost at bad reduction.

Synthesis (PI): the local GL₂ Frobenius datum is formalized as a `2 × 2` matrix constrained by
Cayley–Hamilton, with trace/determinant carrying the Hecke eigenvalue and the cyclotomic value.
This is the algebraic half of the correspondence; the analytic half (Deligne's Weil bound) is in
`Catalog.Novelty.DeligneBoundGL2`, which imports this file.
-/

open Polynomial Matrix

namespace EichlerShimuraGL2

/-- The Hecke / Frobenius characteristic polynomial `X² − a·X + b`.
For a weight-2 eigenform, `a` is the Hecke eigenvalue `a_p` and `b` is the prime `p`. -/
noncomputable def heckePoly {R : Type*} [CommRing R] (a b : R) : R[X] := X ^ 2 - C a * X + C b





/-- The **Frobenius companion matrix** with trace `a` and determinant `p`:
a concrete realization of the local Frobenius datum. -/
def frobMatrix {R : Type*} [CommRing R] (a p : R) : Matrix (Fin 2) (Fin 2) R :=
  !![0, -p; 1, a]




end EichlerShimuraGL2


