-- Prove2me | Definitions.Def_Logic_DenseFinalStepCarryChain
-- name    : Logic_DenseFinalStepCarryChain
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:53:52.224073+00:00
-- url     : https://prove2.me/theorems/69546e14-c741-46b2-bdb4-852b89877891
-- title:
--   Aether Catalog definitions — Logic_DenseFinalStepCarryChain
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.DenseFinalStepCarryChain`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/DenseFinalStepCarryChain.lean by skeleton subtraction
import Mathlib
/-
# NET-25 / Catalog·Logic — Carry-chain automata: the transition is length-general

Formal counterpart of the *transition half* of the NET-25 law
**DENSE-FINAL-STEP-IS-THE-CURE**.

The empirical round (round-net-25, mechanism dissection of the NET-24
stateful-carry-cell cure) measured that in every arm — including the arms whose
full-sequence accuracy at `n = 8` collapsed to `0.002–0.08` — the *final-carry*
probe stayed at `0.86–0.99`.  In other words the recurrent **carry transition**
never lost length-generality; only the **digit readout** at the boundary step
did.

This file makes the transition half a theorem, in the exact sense that is needed
for the mechanism argument:

* `Logic.CarryChain.carry` / `digitOut` — the LSB-first base-`b` addition
  automaton with a one-bit state (`carry_le_one`);
* `Logic.CarryChain.val_digitOut_add_carry` — the *exact* length-general
  invariant: for **every** unroll depth `n`,
  `val d n + c n * b ^ n = val a n + val b n`;
* `Logic.CarryChain.modelStep_eq_*` — a *local-to-global* transfer theorem: any
  learned step function that is pointwise correct on the finitely many reachable
  triples `(x, y, c)` with `x, y < base`, `c ≤ 1` — i.e. exactly the triples a
  training set of depth `≥ 2` already exercises — is automatically correct at
  **every** depth;
* `Logic.CarryChain.exists_lengthGeneral_step` and
  `Logic.CarryChain.no_expressivity_wall` — consequently the observed length
  wall is *not* an expressivity obstruction of the recurrent cell: a correct
  finite step table exists and generalises to all lengths.

The complementary *boundary* half (why a 20-dimensional EOS input and a
384-dimensional one, with byte-identical cell weights, nevertheless train to
different solutions) is in `Logic.DenseFinalStepBoundaryConditioning`.
-/


namespace Logic.CarryChain

open Finset

/-! ## The carry automaton -/

/-- Carry state of LSB-first base-`base` addition of the digit streams `a`, `b`,
after `i` steps.  The state before the first step is `0`. -/
def carry (base : ℕ) (a b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (a i + b i + carry base a b i) / base

/-- Digit emitted at step `i`. -/
def digitOut (base : ℕ) (a b : ℕ → ℕ) (i : ℕ) : ℕ :=
  (a i + b i + carry base a b i) % base

/-- Value of the first `n` LSB-first base-`base` digits of the stream `f`. -/
def val (base : ℕ) (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ range n, f i * base ^ i




/-! ## The exact, depth-uniform invariant -/



/-! ## Local-to-global transfer for a *learned* step function -/

/-- Carry state produced by an arbitrary step function `T : x → y → c → (digit, carry)`. -/
def modelCarry (T : ℕ → ℕ → ℕ → ℕ × ℕ) (a b : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (T (a i) (b i) (modelCarry T a b i)).2

/-- Digit emitted by an arbitrary step function. -/
def modelDigit (T : ℕ → ℕ → ℕ → ℕ × ℕ) (a b : ℕ → ℕ) (i : ℕ) : ℕ :=
  (T (a i) (b i) (modelCarry T a b i)).1

/-- The finitely many *reachable* input triples of the carry cell. -/
def Reachable (base : ℕ) (x y c : ℕ) : Prop := x < base ∧ y < base ∧ c ≤ 1

/-- A step function is *locally correct* if it matches the true transition on
every reachable triple.  For base 10 there are only `10 * 10 * 2 = 200` such
triples, all of which are exercised by depth-`≥ 2` training data. -/
def LocallyCorrect (base : ℕ) (T : ℕ → ℕ → ℕ → ℕ × ℕ) : Prop :=
  ∀ x y c, Reachable base x y c → T x y c = ((x + y + c) % base, (x + y + c) / base)






/-! ## Lab notes (round-net-25, measured)

Teacher-forced evaluation, plain `n = 5` LSB-first base-10 `a + b = c`,
`bs = 256`, 12000 AdamW steps, 2048 fresh draws per evaluation length.

| arm              | params  | n=8 full        | final-carry probe |
|------------------|---------|-----------------|-------------------|
| cap384-raw s0/s1 | 471,582 | 0.0078 / 0.0063 | 0.86–0.99         |
| proj384  s0/s1   | 335,242 | 1.0000 / 1.0000 | 0.86–0.99         |
| pos28    s0/s1   | 129,830 | 0.0049 / 0.0049 | 0.86–0.99         |
| pad384   s0..s3  | 335,242 | 1.0000 × 4      | 0.86–0.99         |
| pad384-zeroEOS   | 334,878 | 0.7441 / 0.0259 | 0.86–0.99         |
| raw20-192 s0..s6 | 125,214 | 0.0806 … 0.0020 | 0.86–0.99         |

The theorems above say the *transition* column of this table has an exact
depth-uniform solution and that local correctness suffices for it; the
`n = 8 full` column therefore isolates a readout/boundary effect, which is what
`Logic.DenseFinalStepBoundaryConditioning` analyses.
-/

end Logic.CarryChain


