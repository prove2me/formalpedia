-- Prove2me | Definitions.Def_Bridges_ClosureKolmogorovRealization
-- name    : Bridges_ClosureKolmogorovRealization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:04.852196+00:00
-- url     : https://prove2.me/theorems/92294d13-f08c-4850-9c72-5fc8081b9d6e
-- title:
--   Aether Catalog definitions — Bridges_ClosureKolmogorovRealization
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ClosureKolmogorovRealization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ClosureKolmogorovRealization.lean by skeleton subtraction
import Mathlib

/-!
# Closure-Kolmogorov Realization Duality via Idempotent Hankel Semimodules

This file establishes a complete realization theory for closure-weighted transductions over
semirings—the analogue of Schützenberger–Fliess realization theory lifted to the
idempotent/closure setting. The core results:

1. **Reconstruction Correctness** (`reconstruction_correct`): A transducer built from a valid
   Hankel presentation faithfully realizes the original bi-series.
2. **Finite Realization** (`finite_closure_realization`): Every bi-series admitting a valid
   finite Hankel presentation is realized by a finite closure transducer.
3. **Reverse Construction** (`transducerToPresentation_valid`): Every transducer canonically
   induces a valid Hankel presentation of its behavior.
4. **Minimality** (`minimal_states_bound`): A minimal-dimension presentation yields a
   transducer with the fewest states among all realizations.
5. **Round-trip Stability** (`roundtrip_behavior`): Reconstruction from the induced
   presentation recovers the original behavior.
6. **Duality** (`duality_object_level`): Realizability by a transducer is equivalent to
   admitting a valid finite Hankel presentation.

## Mathematical Overview

Given a bi-series `f : List A → List B → S` over a semiring `S`, where `A` is the input
alphabet and `B` is the output alphabet, define the *bi-Hankel row* at `(u, v)` as the
function `(u', v') ↦ f(u ++ u', v ++ v')`. The *row semimodule* is the span of all such
rows. If it is finitely generated and stable under residual actions (prepending input/output
symbols), then `f` admits a *finite Hankel presentation*.

The **realization theorem** constructs a closure transducer with `n` states whose behavior
equals `f`. The **minimality theorem** shows this is optimal: no transducer can realize `f`
with fewer states than the minimal presentation dimension.

This is the closure-automata analogue of the Kalman–Schützenberger realization theorem.
-/

open Finset BigOperators

namespace ClosureKolmogorov

/-! ## Matrix-Vector Algebra -/

/-- Matrix-vector multiplication: `(M · v)_j = ∑_i M_{j,i} · v_i`. -/
def matVecMul {n : ℕ} {S : Type*} [Semiring S]
    (M : Fin n → Fin n → S) (v : Fin n → S) : Fin n → S :=
  fun j => ∑ i : Fin n, M j i * v i

/-- Dot product of two vectors: `v · w = ∑_i v_i · w_i`. -/
def dot {n : ℕ} {S : Type*} [Semiring S] (v w : Fin n → S) : S :=
  ∑ i : Fin n, v i * w i

/-- Process a list of symbols through action matrices (right fold):
    `runSymbols act [a₁, …, aₘ] w = act(a₁) · (act(a₂) · (⋯ · (act(aₘ) · w)))`. -/
def runSymbols {n : ℕ} {S : Type*} [Semiring S] {α : Type*}
    (act : α → Fin n → Fin n → S) : List α → (Fin n → S) → (Fin n → S)
  | [], w => w
  | a :: as, w => matVecMul (act a) (runSymbols act as w)



/-! ## Closure Transducer -/

/-- A **closure transducer** with `n` states, input alphabet `A`, output alphabet `B`,
    and weights in a semiring `S`. -/
structure ClosureTransducer (A B S : Type*) [Semiring S] where
  /-- Number of states -/
  n : ℕ
  /-- Initial weight vector -/
  init : Fin n → S
  /-- Input symbol action matrices -/
  actA : A → Fin n → Fin n → S
  /-- Output symbol action matrices -/
  actB : B → Fin n → Fin n → S
  /-- Output (observation) weight vector -/
  out : Fin n → S

variable {A B S : Type*} [Semiring S]

/-- The **behavior** of a closure transducer on input word `u` and output word `v`. -/
def behavior (T : ClosureTransducer A B S) (u : List A) (v : List B) : S :=
  dot (runSymbols T.actA u (runSymbols T.actB v T.init)) T.out

/-! ## Hankel Presentation -/

/-- A **finite Hankel presentation** encodes the algebraic data needed to reconstruct a
    closure transducer from a bi-series. -/
structure HankelPresentation (A B S : Type*) [Semiring S] where
  /-- Basis dimension (number of generators) -/
  n : ℕ
  /-- Coefficient function decomposing each bi-Hankel row in the basis -/
  coeff : List A → List B → Fin n → S
  /-- Input residual action matrices -/
  actA : A → Fin n → Fin n → S
  /-- Output residual action matrices -/
  actB : B → Fin n → Fin n → S
  /-- Initial weight vector -/
  initVec : Fin n → S
  /-- Output weight vector -/
  outVec : Fin n → S

/-- A presentation `P` is **valid** for a bi-series `f` when the action tables and
    boundary vectors correctly decompose `f` through the coefficient function. -/
structure ValidPresentation (P : HankelPresentation A B S) (f : List A → List B → S) :
    Prop where
  /-- The initial vector equals the coefficient at the empty word pair -/
  init_eq : P.initVec = P.coeff [] []
  /-- Input residual compatibility: prepending `a` to the input acts by `actA a` -/
  input_compat : ∀ (a : A) (u : List A) (v : List B) (j : Fin P.n),
    P.coeff (a :: u) v j = ∑ i : Fin P.n, P.actA a j i * P.coeff u v i
  /-- Output residual compatibility at empty input -/
  output_compat : ∀ (b : B) (v : List B) (j : Fin P.n),
    P.coeff [] (b :: v) j = ∑ i : Fin P.n, P.actB b j i * P.coeff [] v i
  /-- Series recovery: `f(u,v) = coeff(u,v) · out` -/
  series_eq : ∀ (u : List A) (v : List B),
    f u v = dot (P.coeff u v) P.outVec

/-! ## Bi-Hankel Row -/


/-! ## Reconstruction -/

/-- Build a closure transducer directly from a Hankel presentation. -/
def reconstructTransducer (P : HankelPresentation A B S) : ClosureTransducer A B S where
  n := P.n
  init := P.initVec
  actA := P.actA
  actB := P.actB
  out := P.outVec


/-! ## Core Lemmas -/

/-
Output-symbol processing on the initial vector yields the empty-input coefficients.
-/

/-
The full run (input then output) computes the coefficient function exactly.
-/

/-! ## Theorem 1: Reconstruction Correctness -/

/-
**Reconstruction Correctness Theorem.** The transducer built from a valid Hankel
    presentation faithfully realizes the original series.
-/

/-! ## Theorem 2: Finite Realization -/



/-! ## Reverse Direction: Transducer → Presentation -/

/-- Construct a Hankel presentation from a transducer by recording state trajectories. -/
def transducerToPresentation (T : ClosureTransducer A B S) : HankelPresentation A B S where
  n := T.n
  coeff := fun u v => runSymbols T.actA u (runSymbols T.actB v T.init)
  actA := T.actA
  actB := T.actB
  initVec := T.init
  outVec := T.out


/-
**Reverse Validity Theorem.** The presentation derived from any transducer is
    valid for that transducer's behavior.
-/

/-! ## Theorem 3: Minimality -/

/-
**Minimality Theorem.** If `P` has the smallest dimension among all valid presentations
    of `f`, then every transducer realizing `f` has at least `P.n` states.
-/

/-! ## Theorem 4: Round-trip Stability -/

/-
**Round-trip Theorem.** Reconstructing a transducer from its induced presentation
    recovers the original behavior.
-/

/-! ## Theorem 5: Realization–Presentation Duality -/

/-
**Duality Theorem.** A bi-series is realizable by a finite closure transducer if and
    only if it admits a valid finite Hankel presentation.
-/

/-! ## Theorem 6: Minimal Realization Existence -/


end ClosureKolmogorov


