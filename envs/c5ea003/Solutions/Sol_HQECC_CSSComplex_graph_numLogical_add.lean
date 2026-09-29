-- Prove2me | solution 1 for HQECC.CSSComplex.graph_numLogical_add
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T11:56:01.353398+00:00
-- url     : https://prove2.me/submissions/a5ed09c9-3da0-472a-9e85-3992c03eb5de

-- Sol generated from Shared/HQECC/CSSHomology.lean
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



/-- Boundaries are cycles: `im d₂ ⊆ ker d₁`. -/
lemma boundaries_le_cycles (X : CSSComplex K A B C) : X.boundaries ≤ X.cycles := by
  rintro _ ⟨a, rfl⟩
  have h := X.comp_eq_zero
  simp only [cycles, LinearMap.mem_ker, ← LinearMap.comp_apply, h, LinearMap.zero_apply]






/-! ## Structural dimension identities -/

/-
Splitting off the boundaries: `dim H + rank d₂ = dim(ker d₁)`.
-/
theorem finrank_homology_add_boundaries [FiniteDimensional K B]
    (X : CSSComplex K A B C) :
    X.numLogical + Module.finrank K (LinearMap.range X.d2) = Module.finrank K X.cycles := by
  convert Submodule.finrank_quotient_add_finrank _;
  · convert LinearEquiv.finrank_eq ( Submodule.comapSubtypeEquivOfLe ( boundaries_le_cycles X ) ) |> Eq.symm;
  · infer_instance;
  · infer_instance;
  · infer_instance

/-
Rank–nullity on `d₁`: `dim(ker d₁) + rank d₁ = dim B`.
-/
theorem finrank_cycles_add_rank_d1 [FiniteDimensional K B]
    (X : CSSComplex K A B C) :
    Module.finrank K X.cycles + Module.finrank K (LinearMap.range X.d1) = Module.finrank K B := by
  rw [ add_comm, ← LinearMap.finrank_range_add_finrank_ker X.d1 ];
  rfl

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
theorem euler [FiniteDimensional K B] [FiniteDimensional K C] (X : CSSComplex K A B C) :
    X.betti0 + Module.finrank K B = Module.finrank K X.cycles + Module.finrank K C := by
  have := Submodule.finrank_quotient_add_finrank ( LinearMap.range X.d1 );
  linarith! [ finrank_cycles_add_rank_d1 X ]

/-
When there are no 2–cells (`d₂ = 0`) the logical space is the full cycle
space: `k = dim(ker d₁)`.  This is the graph/`HQECC` situation.
-/
theorem numLogical_of_d2_eq_zero [FiniteDimensional K B]
    (X : CSSComplex K A B C) (h : X.d2 = 0) :
    X.numLogical = Module.finrank K X.cycles := by
  convert finrank_homology_add_boundaries X
  simp [h, LinearMap.range_zero]

/-
**Graph HQECC count.**  For a graph complex (`d₂ = 0`) the number of logical
qubits equals `E − V + β₀`, in additive form `k + V = E + β₀`.  With `V = dim C`,
`E = dim B`, `β₀ = betti0`.
-/


/-! ## Examples and sanity checks -/




open HQECC in
theorem solution[FiniteDimensional K B] [FiniteDimensional K C]
    (X : CSSComplex K A B C) (h : X.d2 = 0) :
    X.numLogical + Module.finrank K C = Module.finrank K B + X.betti0 := by
  rw [ numLogical_of_d2_eq_zero X h, add_comm ];
  convert euler X |> Eq.symm using 1 ; ring!;
  exact add_comm _ _
