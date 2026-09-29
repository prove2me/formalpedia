-- Prove2me | Theorems.Thm_HQECC_CSSComplex_graph_numLogical_add
-- name    : HQECC.CSSComplex.graph_numLogical_add
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:40:01.141352+00:00
-- url     : https://prove2.me/theorems/80c0ed0f-137d-4c8c-a83e-93e31f5411e0
-- title:
--   Graph numLogical add
-- statement:
--   Formal statement of `HQECC.CSSComplex.graph_numLogical_add` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem HQECC.CSSComplex.graph_numLogical_add[FiniteDimensional K B] [FiniteDimensional K C]
--       (X : CSSComplex K A B C) (h : X.d2 = 0) :
--       X.numLogical + Module.finrank K C = Module.finrank K B + X.betti0 := by sorry
--
--   /-! ## Examples and sanity checks -/
--
--
--
--   #check @CSSComplex.numLogical_add
--   #check @CSSComplex.euler
--   #check exRep
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/HQECC/CSSHomology.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/HQECC/CSSHomology.lean#L169

-- Thm stub generated from Shared/HQECC/CSSHomology.lean
import Mathlib
import Definitions.Def_Shared_HQECC_CSSHomology

open HQECC

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


open CSSComplex

variable {K A B C : Type*} [Field K]
  [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]









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

theorem HQECC.CSSComplex.graph_numLogical_add[FiniteDimensional K B] [FiniteDimensional K C]
    (X : CSSComplex K A B C) (h : X.d2 = 0) :
    X.numLogical + Module.finrank K C = Module.finrank K B + X.betti0 := by sorry
