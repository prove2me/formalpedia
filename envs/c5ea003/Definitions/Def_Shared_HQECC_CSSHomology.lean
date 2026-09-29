-- Prove2me | Definitions.Def_Shared_HQECC_CSSHomology
-- name    : Shared_HQECC_CSSHomology
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:53:53.924696+00:00
-- url     : https://prove2.me/theorems/4253423d-eb26-44a1-9bc2-a38ce379e5bc
-- title:
--   Aether Catalog definitions — Shared_HQECC_CSSHomology
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.HQECC.CSSHomology`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/HQECC/CSSHomology.lean by skeleton subtraction
import Mathlib

namespace HQECC

/-!
# CSS codes as homology: the dimension of the logical space

A Calderbank–Shor–Steane (CSS) quantum code is built from two classical linear
codes over `𝔽₂` whose parity checks anticommute; equivalently it is a length–two
segment of a chain complex

  `A --d₂--> B --d₁--> C`,   with   `d₁ ∘ d₂ = 0`.

The physical qubits are indexed by (a basis of) the middle space `B`.  The space
of **logical qubits** is exactly the middle homology

  `H = ker d₁ / im d₂ = Z / Bd`,

so *the number of logical qubits is a homological invariant*.  This file develops
that dictionary abstractly over an arbitrary field and proves the two structural
identities underlying every CSS/HQECC computation:

* `CSSComplex.numLogical_add` — the **dimension formula**
    `dim H + rank d₁ + rank d₂ = dim B`,
  i.e. `k = n − rank(H_X) − rank(H_Z)`, the CSS count of logical qubits.
* `CSSComplex.euler` — the **Euler characteristic identity**
    `dim H⁰ + dim B = dim(ker d₁) + dim C`,
  which for a graph complex is `χ = V − E = β₀ − β₁`.

These are the engine behind the homological quantum error correcting code
`HQECC(K)` of a simplicial complex, instantiated for the hypercube in
`HypercubeCode.lean`.

-- !-- Lab Notes -- !--
HYPOTHESIS (Hypothesizer).  "Quantum error correction is cohomology": the CSS
recipe `k = dim C₁ − dim C₂` with `C₂ ⊆ C₁` is literally the dimension of a
quotient module `C₁/C₂`, hence of a homology group.  If we package the two
parity check matrices as a two–step chain complex, the number of logical qubits
should be *forced* to equal `dim(ker d₁) − dim(im d₂)` and, by rank–nullity, to
`dim B − rank d₁ − rank d₂`.

EXPERIMENT (Experimenter).  We define `CSSComplex`, its `cycles = ker d₁`,
`boundaries = im d₂`, and `homology = cycles / boundaries`.  Two applications of
rank–nullity (`Submodule.finrank_quotient_add_finrank`,
`LinearMap.finrank_range_add_finrank_ker`) plus the isomorphism
`Submodule.comapSubtypeEquivOfLe` give the dimension formula and the Euler
identity as clean additive equalities over ℕ (no truncated subtraction).

ANALYSIS (Analyst).  Working with the *additive* form of rank–nullity avoids all
ℕ–subtraction pitfalls and makes the results field–agnostic.  The homology is a
genuine quotient type, not a renamed definition, so the theorems are not
definitional.

CRITIQUE (Critic).  The only subtlety is that `homology` is defined as a quotient
of `cycles` by `boundaries.comap cycles.subtype`; we must show this comap has the
same dimension as `boundaries`, which is exactly `comapSubtypeEquivOfLe` applied
to `boundaries_le_cycles`.  No theorem here is vacuous or proved by `decide`.
-/

open Module LinearMap

/-- A length–two chain complex `A --d₂--> B --d₁--> C` with `d₁ ∘ d₂ = 0`.
This is the algebraic skeleton of a CSS quantum code: the middle space `B`
carries the physical qubits, `d₁` is the `X`-type parity check and `d₂ᵀ` the
`Z`-type parity check. -/
structure CSSComplex (K : Type*) [Field K]
    (A B C : Type*) [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
    [AddCommGroup C] [Module K C] where
  /-- The second boundary map (whose image is the space of boundaries). -/
  d2 : A →ₗ[K] B
  /-- The first boundary map (whose kernel is the space of cycles). -/
  d1 : B →ₗ[K] C
  /-- The defining chain-complex condition `d₁ ∘ d₂ = 0`. -/
  comp_eq_zero : d1.comp d2 = 0

namespace CSSComplex

variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

/-- The **cycles** `Z = ker d₁`. -/
def cycles (X : CSSComplex K A B C) : Submodule K B := LinearMap.ker X.d1

/-- The **boundaries** `Bd = im d₂`. -/
def boundaries (X : CSSComplex K A B C) : Submodule K B := LinearMap.range X.d2


/-- The **logical space** = middle homology `H = ker d₁ / im d₂`. -/
noncomputable def homology (X : CSSComplex K A B C) : Type _ :=
  X.cycles ⧸ (X.boundaries.comap X.cycles.subtype)

noncomputable instance (X : CSSComplex K A B C) : AddCommGroup X.homology :=
  inferInstanceAs (AddCommGroup (X.cycles ⧸ _))

noncomputable instance (X : CSSComplex K A B C) : Module K X.homology :=
  inferInstanceAs (Module K (X.cycles ⧸ _))

/-- The number of **logical qubits** of the code, `k = dim H`. -/
noncomputable def numLogical (X : CSSComplex K A B C) : ℕ := Module.finrank K X.homology

/-- The **zeroth homology** `H⁰ = C / im d₁` (for a graph complex, the number of
connected components `β₀`). -/
noncomputable def betti0 (X : CSSComplex K A B C) : ℕ :=
  Module.finrank K (C ⧸ LinearMap.range X.d1)

/-! ## Structural dimension identities -/

/-
Splitting off the boundaries: `dim H + rank d₂ = dim(ker d₁)`.
-/

/-
Rank–nullity on `d₁`: `dim(ker d₁) + rank d₁ = dim B`.
-/

/-
**CSS dimension formula.**  The number of logical qubits is
`k = dim B − rank d₁ − rank d₂`, stated additively.  This is exactly the CSS
count `k = n − rank(H_X) − rank(H_Z)`.
-/

/-
**Euler characteristic identity.**  `dim H⁰ + dim B = dim(ker d₁) + dim C`.
For a graph complex `B = 𝔽₂^E`, `C = 𝔽₂^V` this reads `β₀ + E = β₁ + V`,
i.e. `V − E = β₀ − β₁`.
-/

/-
When there are no 2–cells (`d₂ = 0`) the logical space is the full cycle
space: `k = dim(ker d₁)`.  This is the graph/`HQECC` situation.
-/

/-
**Graph HQECC count.**  For a graph complex (`d₂ = 0`) the number of logical
qubits equals `E − V + β₀`, in additive form `k + V = E + β₀`.  With `V = dim C`,
`E = dim B`, `β₀ = betti0`.
-/

end CSSComplex

/-! ## Examples and sanity checks -/

section Examples


end Examples
end HQECC


