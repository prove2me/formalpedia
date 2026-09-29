-- Prove2me | Definitions.Def_Novelty_FiniteHeightConverse
-- name    : Novelty_FiniteHeightConverse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:25:37.986117+00:00
-- url     : https://prove2.me/theorems/30c0a09c-6576-4587-8bf8-71410626ad70
-- title:
--   Aether Catalog definitions — Novelty_FiniteHeightConverse
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FiniteHeightConverse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FiniteHeightConverse.lean by skeleton subtraction
import Mathlib
/-
# A Converse to "Finite Height ⟹ Semistable" for p-adic Galois Representations

## Domain: Novelty (p-adic Hodge theory / Breuil–Kisin modules)

This file develops the **honest finite-dimensional linear-algebra core** of the theory of
*finite-height* `p`-adic Galois representations and its relationship to *semistability*,
in the spirit of Kisin's classification of semistable representations by Breuil–Kisin
modules and of Liu's work on representations of finite `E(u)`-height
(cf. arXiv:2404.19603 and T. Liu, *Torsion p-adic Galois representations and a conjecture
of Fontaine*).

### The real-geometry picture (informal)

Let `K/ℚ_p` be a finite extension with ring of integers `O_K`, residue field `k`, and a
fixed uniformizer `π` with Eisenstein minimal polynomial `E(u)` over `W(k)[1/p]`.  Put
`𝔖 = W(k)[[u]]` with the Frobenius `φ : u ↦ u^p`.  A **Breuil–Kisin module** is a finite
free `𝔖`-module `𝔐` with a `φ`-semilinear `φ_𝔐 : 𝔐 → 𝔐` whose linearization
`Φ : φ*𝔐 → 𝔐` is injective with cokernel killed by a power of `E(u)`.  The minimal such
power is the **`E`-height** of `𝔐`.

* Kisin's theorem: lattices in **semistable** (resp. crystalline) `G_K`-representations with
  Hodge–Tate weights in `[0, h]` correspond to Breuil–Kisin modules of `E`-height `≤ h`.
  So *"finite height"* is the lattice-theoretic shadow of *"semistable with bounded weights"*.
* The implication **finite height ⟹ semistable Newton/étale behaviour** is the "easy"
  half: a Frobenius lattice of finite height becomes an isomorphism after inverting `E`
  (i.e. away from the special divisor), so the generic `(φ,Γ)`/Galois datum is honest.
* The interesting **converse** — *if the Frobenius is generically an isomorphism (its
  Newton slopes are concentrated at `E`), then a genuine finite-height lattice exists* — is
  exactly what makes finite-height theory usable: it manufactures the Breuil–Kisin lattice
  from a purely generic (étale) condition.

### What is honestly provable here

Choosing a basis turns the linearized Frobenius `Φ` into a square matrix `A ∈ Mₙ(𝔖)`.  The
height condition "`E^h · 𝔐 ⊆ Φ(𝔐)`" becomes the matrix statement "`∃ B, A·B = E^h·I` and
`B·A = E^h·I`", and the generic/Newton condition "`Φ` is an isomorphism after inverting `E`"
becomes "`det A` divides some power of `E`".  In this exact finite shadow we prove, over an
arbitrary commutative (coefficient) ring `𝔖`:

* `BKModule.finiteHeight_iff_newton` — the **equivalence**
  `FiniteHeight ↔ NewtonConcentrated`, whose nontrivial (⟸) direction is the **converse**.
* `BKModule.newton_implies_finiteHeight` — the headline **converse**, with the explicit
  height bound `h ≤ N` whenever `det A ∣ E^N` (the lattice-theoretic shadow of
  "Hodge–Tate weights ≤ N").  Construction: `B := c • adjugate A` where `det A · c = E^N`.
* `BKModule.finiteHeight_implies_newton` — the easy forward implication (the shadow of
  "finite height ⟹ semistable"), with `N = h · rank`.
* `BKModule.hasHeightLE_zero_iff` — **height `0` = étale = unramified**: a module has height
  `0` iff `det A` is a unit (`Φ` is already an isomorphism integrally).
* `BKModule.hasHeightLE_mono` — heights only grow: `≤ h ⟹ ≤ h'` for `h ≤ h'`.
* `BKModule.finiteHeight_directSum` — finite height is closed under `⊕`
  (Whitney sum of Breuil–Kisin modules), via `det(𝔐 ⊕ 𝔑) = det 𝔐 · det 𝔑`.
* `BKModule.finiteHeight_iff_det` — finite height is **detected by the determinant**, i.e.
  by the rank-one *Hodge–Tate determinant* `∧ᵗᵒᵖ 𝔐` (a faithful shadow of the fact that the
  determinant of a semistable representation is the cyclotomic-twist datum carrying the
  total Hodge–Tate weight).

Non-vacuity is witnessed over `𝔖 = ℚ[X]`, `E = X`:
`example_finiteHeight` (`[X²]` has finite height), `example_etale` (`[1]` has height `0`),
and `example_not_finiteHeight` (`[X+1]` has **no** finite height, since `X+1 ∤ X^N`: the
Frobenius degenerates *away* from the special divisor, so no Breuil–Kisin lattice exists).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): "finite height" is usually packaged as the existence of a
Frobenius lattice with `E`-bounded cokernel — a condition that *looks* like it quantifies
over the whole module.  Bold claim: it is equivalent to a single **determinantal** Newton
condition `det Φ ∣ E^N`, i.e. the Frobenius is an isomorphism exactly away from the special
divisor `V(E)`.  If true, the deep half "semistable ⟹ finite height lattice" has a clean
exact-linear-algebra shadow whose converse direction is *constructive* (adjugate formula).

Experiment (Experimenter): modelled `𝔐` by its Frobenius matrix `A`.  Forward
(`finite height ⟹ Newton`): take `det` of `A·B = E^h·I`, giving `det A · det B = (E^h)^rank`,
so `det A ∣ E^{h·rank}`.  Converse (`Newton ⟹ finite height`): write `E^N = det A · c` and
set `B = c • adjugate A`; then `A·B = c•(A·adjugate A) = c•(det A • I) = E^N • I` and
symmetrically `B·A`, using `Matrix.mul_adjugate`/`Matrix.adjugate_mul`.  Height `0` is read
off `Matrix.isUnit_iff_isUnit_det`.  Direct sums use `Matrix.det_fromBlocks_zero₂₁`.
The negative example uses polynomial evaluation at `-1` to show `X+1 ∤ X^N`.

Analysis (Analyst): the equivalence is *sharp*.  The explicit bound — finite height `≤ N`
whenever `det A ∣ E^N` — is the lattice shadow of "Hodge–Tate weights `≤ N`", and the
forward bound `N = h·rank` is the determinant accumulating one weight per basis vector.  The
load-bearing hypothesis is genuinely the *divisibility* `det A ∣ E^N`: the counterexample
`[X+1]` shows that a perfectly good integral Frobenius with **non**-`E` determinant has no
finite height, i.e. the Newton condition is not automatic — exactly why the converse is a
theorem and not a formality.

Critique (Critic): is anything vacuous?  No.  `newton_implies_finiteHeight` produces an
honest two-sided `B` (not via a contradiction), `finiteHeight_iff_det` is a real `Iff`, and
the three worked examples (positive, étale, negative) pin down both directions over `ℚ[X]`.
Corner case `rank = 0`: everything holds (empty matrices, `det = 1`), faithfully — the zero
representation is crystalline of height `0`.  Coefficient generality: we only need `CommRing
𝔖`; no domain/Noetherian/`p`-adic hypotheses are smuggled in, so the shadow is as clean as
the linear algebra allows.

Synthesis (PI): the catalog's GL(1)/GL(2) local-datum files (`GaloisDuality`,
`EichlerShimuraGL2`, `DeligneBoundGL2`) describe Frobenius eigenvalues *on the generic
fibre*.  This file supplies the **integral / lattice** counterpart: a Frobenius lattice is
of finite height iff its determinant's Newton slopes sit at the special divisor, with the
converse manufacturing the Breuil–Kisin lattice constructively.  Together they sketch both
the analytic (Weil bound) and integral (finite height) faces of local `p`-adic Hodge data.
-- !-- end Lab Notes -- !--
-/

open Matrix

namespace BKModule

/-- A **Breuil–Kisin module** over a coefficient ring `S`, presented by the matrix `frob`
of its linearized Frobenius `Φ : φ*𝔐 → 𝔐` in a chosen basis.  (The Eisenstein element `E`
and the semilinearity of `φ` are external data; in this exact shadow all height/Newton
information is carried by the matrix `frob` and the chosen `E`.) -/
structure _root_.BKModule (S : Type*) [CommRing S] where
  /-- The rank of the underlying finite free `𝔖`-module. -/
  rank : ℕ
  /-- The matrix of the linearized Frobenius in a chosen basis. -/
  frob : Matrix (Fin rank) (Fin rank) S

variable {S : Type*} [CommRing S]

/-- `𝔐` has **`E`-height `≤ h`**: the cokernel of the Frobenius is killed by `E^h`, i.e.
`E^h · 𝔐 ⊆ Φ(𝔐)` with a two-sided integral witness `B`. -/
def HasHeightLE (M : BKModule S) (E : S) (h : ℕ) : Prop :=
  ∃ B : Matrix (Fin M.rank) (Fin M.rank) S,
    M.frob * B = (E ^ h) • (1 : Matrix (Fin M.rank) (Fin M.rank) S) ∧
    B * M.frob = (E ^ h) • (1 : Matrix (Fin M.rank) (Fin M.rank) S)

/-- `𝔐` is of **finite height** if some `E^h` kills the Frobenius cokernel. -/
def FiniteHeight (M : BKModule S) (E : S) : Prop := ∃ h, M.HasHeightLE E h

/-- The **Newton condition**: `det Φ` divides a power of `E`, i.e. the Frobenius becomes an
isomorphism after inverting `E` (its Newton slopes are concentrated at the special divisor
`V(E)`).  This is the étale/semistable-Newton shadow. -/
def NewtonConcentrated (M : BKModule S) (E : S) : Prop := ∃ N, M.frob.det ∣ E ^ N







/-- The **Whitney sum** `𝔐 ⊕ 𝔑` of two Breuil–Kisin modules: block-diagonal Frobenius. -/
def directSum (M N : BKModule S) : BKModule S where
  rank := M.rank + N.rank
  frob := (Matrix.reindex finSumFinEquiv finSumFinEquiv
            (Matrix.fromBlocks M.frob 0 0 N.frob))


/-- An **extension** `0 → 𝔐 → 𝔈 → 𝔑 → 0` of Breuil–Kisin modules, presented by the
block-upper-triangular Frobenius `[[A, U], [0, C]]` (the off-diagonal block `U` records the
extension class). -/
def extension {m n : ℕ} (A : Matrix (Fin m) (Fin m) S) (U : Matrix (Fin m) (Fin n) S)
    (C : Matrix (Fin n) (Fin n) S) : BKModule S where
  rank := m + n
  frob := Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A U 0 C)


/-- The **dual** Breuil–Kisin module `𝔐^∨`, presented by the adjugate of the Frobenius
(the integral form of `(det Φ) · Φ⁻¹`). -/
def dual (M : BKModule S) : BKModule S := ⟨M.rank, M.frob.adjugate⟩


/-! ### Worked examples over `𝔖 = ℚ[X]`, `E = X` (non-vacuity) -/




end BKModule


