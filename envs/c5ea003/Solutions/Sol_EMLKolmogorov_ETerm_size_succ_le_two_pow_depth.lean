-- Prove2me | solution 1 for EMLKolmogorov.ETerm.size_succ_le_two_pow_depth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:23:07.087688+00:00
-- url     : https://prove2.me/submissions/89f6ab95-ec57-4654-b579-6e85931b3e7e

-- Sol generated from EML/KolmogorovComplexityBound.lean
import Mathlib
import Definitions.Def_EML_KolmogorovComplexityBound
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# EML Complexity is a Kolmogorov Measure: Finiteness and Incompressibility

This file is a research contribution to the **EML (Exponential–Multiplicative–Logarithmic)
universal approximation** programme. The density files
(`EML.ExponentialPolynomialDensity`, `EML.StoneWeierstrassApprox`) prove the *qualitative*
side — every continuous function on a compact set is uniformly approximable by EML terms.
The mission asks for the *quantitative* side: a complexity theory of EML representations
**connecting to Kolmogorov complexity**.

We make that connection rigorous. We introduce the **constant-free EML term algebra**
`ETerm` (`var`, `+`, `×`, `exp`, `log`). Because the alphabet is finite, this is a
*countable* syntactic class, so each constructor `size`/`depth` becomes a genuine
**description length**. We prove the two structural pillars of Kolmogorov complexity,
instantiated to EML:

* **Counting / finiteness** (`finite_computableLE`, `finite_computableDepthLE`): for every
  size budget `n` (resp. depth budget `d`) only *finitely many* functions `ℝ → ℝ` are
  *exactly* EML-representable within that budget. This is the EML form of the statement
  "there are at most `2^{n+1}` programs of length `n`".
* **Incompressibility** (`exists_incompressible`, `exists_incompressible_depth`): for every
  budget there exists a function that **no** EML term within that budget computes. Most
  functions are incompressible — exactly the Kolmogorov counting lower bound.

Two further Kolmogorov hallmarks are proved:

* **Subadditivity** (`K_add_le`, `K_mul_le`, `K_exp_le`, `K_log_le`): the EML complexity
  `K f` (minimal term size computing `f`) satisfies `K (f+g) ≤ K f + K g + 1`, etc. — the
  "concatenation of programs" inequalities.
* **Depth ≤ size tower** (`size_succ_le_two_pow_depth`): a depth-`d` term has size below
  `2^{d+1}`, so a depth budget is a (much coarser) description length, and depth
  incompressibility follows from size incompressibility.

-- !-- Lab Notes -- !--
HYPOTHESIS (K1). EML term `size` is a Kolmogorov description length: the number of
functions exactly representable below any fixed size is finite, hence "most" functions are
incompressible. HYPOTHESIS (K2, surprising). The same holds for *depth* even though a fixed
depth allows unboundedly wide (large-size) terms — because depth bounds size by a tower
`size < 2^{depth+1}`. HYPOTHESIS (K3). `K` is subadditive under all EML constructors.

EXPERIMENT. Defined `ETerm` with `eval`, `size`, `depth`. Proved `finite_termsLE n` by
strong induction via the constructor inclusion `{t | size ≤ n+1} ⊆ {var} ∪ image2 add S S ∪
image2 mul S S ∪ expOf '' S ∪ logOf '' S` with `S = {t | size ≤ n}`; pushed through `eval`
to get `finite_computableLE`. Incompressibility = a finite set cannot exhaust the infinite
type `ℝ → ℝ` (constants inject). Subadditivity = `Nat.sInf` is attained, then build the
compound term. Depth: `size + 1 ≤ 2^{depth+1}` by induction, giving `depthLE d ⊆ sizeLE 2^{d+1}`.

ANALYSIS. K1, K2, K3 all confirmed. The crux is that *constant-freeness* makes the alphabet
finite; with real constants the class is uncountable and counting collapses (see FAILURE).

INSIGHT. Density and incompressibility are not in tension: density needs the *union* over
all budgets (complexity → ∞), each budget being a finite island. This is precisely
"universal approximation with a complexity price", the quantitative half of the mission.

FAILURE ANALYSIS. A first draft kept a real-valued `const c` leaf. Then `{t | size ≤ 1}`
is already uncountable (`{const c}`), so `finite_termsLE` is *false*. Diagnosis: Kolmogorov
counting requires a finite description alphabet; we dropped `const` and recover all needed
expressivity through `var`, `add`, `exp`, `log` (e.g. `exp(x+⋯+x) = e^{kx}`).

CRITIQUE. Are the theorems vacuous? No: `computableLE n` is nonempty (`var ∈`) and strictly
grows, and the incompressible witness is a genuine function. `K_add_le` uses attainment of
`Nat.sInf`, not a definitional trick.
-/

noncomputable section
open Set

open EMLKolmogorov


open ETerm





/-
A depth-`d` term has size below `2^{d+1}`: depth bounds size by a tower.
-/


open ETerm







/-! ### Counting / finiteness: the heart of the Kolmogorov lower bound -/

/-
**Counting bound (terms).** Only finitely many terms have size `≤ n`.
-/


/-
Depth budgets are size budgets: a depth-`d` term has size `≤ 2^{d+1}`.
-/



/-! ### Incompressibility: most functions need more than any fixed budget -/

/-
`ℝ → ℝ` is infinite (constants inject).
-/

/-
**Incompressibility (size).** For every size budget `n` there is a function that no
EML term of size `≤ n` computes.
-/

/-
**Incompressibility (depth).** For every depth budget `d` there is a function that no
EML term of depth `≤ d` computes.
-/

/-! ### Subadditivity of EML Kolmogorov complexity -/



/-
**Subadditivity under `+`**: `K (f + g) ≤ K f + K g + 1`.
-/

/-
**Subadditivity under `×`**: `K (f * g) ≤ K f + K g + 1`.
-/

/-
**Subadditivity under `exp`**: `K (exp ∘ f) ≤ K f + 1`.
-/

/-
**Subadditivity under `log`**: `K (log ∘ f) ≤ K f + 1`.
-/


open EMLKolmogorov.ETerm in
theorem solution(t : ETerm) : t.size + 1 ≤ 2 ^ (t.depth + 1) := by
  induction' t with t ih;
  · decide +revert;
  · simp +arith +decide [ ETerm.size, ETerm.depth ];
    cases max_cases t.depth ih.depth <;> simp_all +decide [ pow_succ' ];
    · linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ‹_› ];
    · linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( by linarith : t.depth ≤ ih.depth ) ];
  · rename_i a b ha hb;
    rw [ show ( a.mul b ).size = a.size + b.size + 1 by rfl, show ( a.mul b ).depth = Max.max a.depth b.depth + 1 by rfl ];
    cases max_cases a.depth b.depth <;> simp_all +decide [ pow_succ' ];
    · linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ‹_› ];
    · linarith [ pow_le_pow_right₀ ( by decide : 1 ≤ 2 ) ( by linarith : a.depth ≤ b.depth ) ];
  · simp +arith +decide [ *, ETerm.size, ETerm.depth ];
    grind;
  · simp +arith +decide [ *, ETerm.size, ETerm.depth ];
    grind
