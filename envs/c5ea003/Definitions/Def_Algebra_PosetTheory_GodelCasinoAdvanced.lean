-- Prove2me | Definitions.Def_Algebra_PosetTheory_GodelCasinoAdvanced
-- name    : Algebra_PosetTheory_GodelCasinoAdvanced
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:49:04.076709+00:00
-- url     : https://prove2.me/theorems/71e75c92-2b0b-4b03-b601-c62e3107e09e
-- title:
--   Aether Catalog definitions — Algebra_PosetTheory_GodelCasinoAdvanced
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.PosetTheory.GodelCasinoAdvanced`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/PosetTheory/GodelCasinoAdvanced.lean by skeleton subtraction
import Mathlib

/-!
# Gödel's Casino: Oracle Hierarchies and Information Value

We develop an advanced theory of Gödel's Casino that formalizes:
1. **Oracle-augmented games** — how strengthening the decidability oracle affects strategy profit
2. **Strategy dominance preorder** — a partial order on strategies
3. **Incompleteness entropy** — an information-theoretic measure of undecidability
4. **Layered Casino** — a multi-round game with escalating oracle strength
5. **Information Value Theorem** — the exact value of decidability information

## Novel Definitions

* `OracleCasino` — a casino parameterized by an oracle (decidability predicate)
* `StrategyDominates` — preorder on strategies measuring worst-case relative performance
* `IncompletenessEntropy` — the fraction of undecidable rounds
* `LayeredCasino` — multi-layer game where each layer has a stronger oracle
* `OracleUnion` — combining two oracles into one

## Main Results

* **Oracle Monotonicity**: Strengthening the oracle never decreases optimal profit
* **Information Value Theorem**: Additional profit = additional decidable rounds
* **Dominance Transitivity**: Strategy dominance is a preorder
* **Layer Profit Monotonicity**: Higher layers yield weakly more profit
* **Entropy-Profit Duality**: Entropy + decidable fraction = 1
* **Oracle Composition**: Union of oracles dominates each component
* **Oracle Query Equivalence**: Profit depends only on COUNT of decidable rounds
* **Binary Casino Zero-Sum**: Fundamental zero-sum property of binary bets

## Cross-domain Connections

* Logic ↔ Information Theory: incompleteness entropy captures information loss
* Game Theory ↔ Order Theory: strategy comparison forms a preorder
* Computability ↔ Game Theory: oracle hierarchy maps to profit hierarchy
-/

noncomputable section

open Finset BigOperators

/-! ## Core Definitions -/

/-- A bet in Gödel's Casino. -/
inductive GBet : Type
  | betTrue  : GBet
  | betFalse : GBet
  | abstain  : GBet
  deriving DecidableEq, Repr

/-- Payoff from a single bet: +1 correct, -1 incorrect, 0 abstain. -/
def gPayoff (truth : Bool) (b : GBet) : ℤ :=
  match b with
  | .abstain  => 0
  | .betTrue  => if truth then 1 else -1
  | .betFalse => if truth then -1 else 1




/-! ## Part I: Oracle Casino -/

/-- An Oracle Casino: statements indexed by `ι` with truth values and
decidability determined by an oracle. -/
structure OracleCasino (ι : Type*) [Fintype ι] where
  truth : ι → Bool
  oracle : ι → Bool

/-- The selective strategy: bet correctly on oracle-decidable rounds, abstain otherwise. -/
def selectiveStrat {ι : Type*} [Fintype ι] (G : OracleCasino ι) (i : ι) : GBet :=
  if G.oracle i then
    if G.truth i then .betTrue else .betFalse
  else .abstain

/-- Profit of a strategy. -/
def casinoProfit {ι : Type*} [Fintype ι] (G : OracleCasino ι) (s : ι → GBet) : ℤ :=
  ∑ i : ι, gPayoff (G.truth i) (s i)

/-- Number of decidable rounds. -/
def decCount {ι : Type*} [Fintype ι] [DecidableEq ι] (G : OracleCasino ι) : ℕ :=
  (Finset.univ.filter (fun i => G.oracle i = true)).card

/-- Number of undecidable rounds. -/
def undecCount {ι : Type*} [Fintype ι] [DecidableEq ι] (G : OracleCasino ι) : ℕ :=
  (Finset.univ.filter (fun i => G.oracle i = false)).card



/-
**Profit Ceiling**: No strategy exceeds `Fintype.card ι` profit.
-/


/-
**Selective Positive**: If any round is decidable, profit > 0.
-/

/-! ## Part II: Decidable-Undecidable Partition -/

/-
Decidable and undecidable counts partition the total.
-/

/-! ## Part III: Incompleteness Entropy -/

/-- **Incompleteness Entropy**: fraction of undecidable rounds.
This measures how much "information" is lost due to incompleteness. -/
def incompletenessEntropy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : OracleCasino ι) : ℚ :=
  (undecCount G : ℚ) / (Fintype.card ι : ℚ)

/-- **Decidable Fraction**: fraction of decidable rounds. -/
def decidableFraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : OracleCasino ι) : ℚ :=
  (decCount G : ℚ) / (Fintype.card ι : ℚ)

/-
**Entropy-Profit Duality**: Incompleteness entropy + decidable fraction = 1.
What incompleteness takes away is exactly what decidability gives.
-/

/-! ## Part IV: Strategy Dominance -/

/-- Strategy `s₁` dominates `s₂` if it achieves ≥ profit on every truth assignment. -/
def StrategyDominates {ι : Type*} [Fintype ι]
    (_oracle : ι → Bool) (s₁ s₂ : ι → GBet) : Prop :=
  ∀ truth : ι → Bool,
    (∑ i, gPayoff (truth i) (s₁ i)) ≥ (∑ i, gPayoff (truth i) (s₂ i))



/-! ## Part V: Oracle Augmentation -/

/-- An augmented casino with base decidability and oracle extension. -/
structure AugmentedCasino (ι : Type*) [Fintype ι] where
  truth : ι → Bool
  baseDec : ι → Bool
  oracleExt : ι → Bool

/-- Combined decidability: base OR oracle. -/
def AugmentedCasino.combined {ι : Type*} [Fintype ι]
    (G : AugmentedCasino ι) (i : ι) : Bool :=
  G.baseDec i || G.oracleExt i

/-- Base decidable count. -/
def AugmentedCasino.baseCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : AugmentedCasino ι) : ℕ :=
  (Finset.univ.filter (fun i => G.baseDec i = true)).card

/-- Combined decidable count. -/
def AugmentedCasino.combinedCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : AugmentedCasino ι) : ℕ :=
  (Finset.univ.filter (fun i => G.combined i = true)).card

/-
**Oracle Extension Monotonicity**: Combined decidability ≥ base decidability.
-/

/-- **Information Value**: Additional decidable rounds from the oracle. -/
def informationValue {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : AugmentedCasino ι) : ℕ :=
  G.combinedCount - G.baseCount


/-! ## Part VI: Layered Casino (Oracle Hierarchy) -/

/-- A Layered Casino: a sequence of oracle levels where each level decides
a superset of the previous level. Models the arithmetic hierarchy. -/
structure LayeredCasino (ι : Type*) [Fintype ι] (L : ℕ) where
  truth : ι → Bool
  oracle : Fin (L + 1) → ι → Bool
  mono : ∀ (k : Fin L) (i : ι),
    oracle ⟨k.val, by omega⟩ i = true → oracle ⟨k.val + 1, by omega⟩ i = true

/-- Profit at a given oracle level. -/
def layerDecCount {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ}
    (G : LayeredCasino ι L) (level : Fin (L + 1)) : ℕ :=
  (Finset.univ.filter (fun i => G.oracle level i = true)).card

/-
**Layer Decidability Monotonicity**: Higher oracle levels decide more.
-/

/-! ## Part VII: Binary Casino Zero-Sum -/

/-- A binary bet (no abstain). -/
inductive BBet : Type
  | yes : BBet
  | no  : BBet
  deriving DecidableEq

/-- Binary payoff. -/
def bPayoff (truth : Bool) (b : BBet) : ℤ :=
  match b with
  | .yes => if truth then 1 else -1
  | .no  => if truth then -1 else 1



/-! ## Part VIII: Oracle Union -/

/-- Union of two oracles. -/
def oracleUnion {ι : Type*} (o₁ o₂ : ι → Bool) : ι → Bool :=
  fun i => o₁ i || o₂ i

/-
**Oracle Union Dominance (left)**: Union decides everything o₁ decides.
-/

/-
**Oracle Union Dominance (right)**: Union decides everything o₂ decides.
-/


/-! ## Part IX: Adversarial Worst Case -/

/-
**Adversarial Worst Case**: If ALL rounds are undecidable, the adversary
can ensure any fixed strategy achieves profit = -n (maximum loss).
-/


/-! ## Part X: Falsifiable Conjecture (Arithmetic Decidability Density)

**Conjecture**: For any finite collection of arithmetic sentences of quantifier
depth at most `k` in the arithmetic hierarchy, the fraction decidable in PA
is at least `1/(2^k)`.

**Testable prediction**: Enumerate Σ₁ sentences up to length 100. At least 50%
should be decidable in PA (since Σ₁-completeness guarantees all true Σ₁ sentences
are provable, and at least half of random Σ₁ sentences are true).

We state a conditional version:
-/


end


