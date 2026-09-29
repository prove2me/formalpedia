-- Prove2me | Definitions.Def_Bridges_OracleCobhamInvariance
-- name    : Bridges_OracleCobhamInvariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T09:49:26.829619+00:00
-- url     : https://prove2.me/theorems/60cbd52e-adfe-4499-8960-93e8852db378
-- title:
--   Aether Catalog definitions — Bridges_OracleCobhamInvariance
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.OracleCobhamInvariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/OracleCobhamInvariance.lean by skeleton subtraction
import Mathlib
/-
# Oracle-Trace Cobham Invariance via Prefix Ultrametrics and Rational Trace Transductions

This file formalizes a **Cobham-style invariance principle for oracle traces**, expressed through
prefix-ultrametric geometry, weighted trace transductions, and semiring-valued trace growth.

## Central Vision

If two oracle-trace models simulate each other through finite-distortion admissible trace
transductions, then their trace-ball structures agree up to explicit additive constants.

## Bridges

- **Implicit complexity / Cobham invariance** — machine-independent complexity classes
- **Ultrametric geometry and entropy** — prefix agreement as non-Archimedean distance
- **Weighted automata / rational transductions** — finite-state complexity surrogates
- **ML certified robustness** — Lipschitz stability of sequence classifiers
- **Post-quantum / lattice cryptographic** complexity via growth exponents of trace balls

## Structures (8 novel types)

- `OracleTrace`, `WeightedTraceTransducer`, `AdmissibleSimulation`, `BiAdmissibleEquiv`
- `PrefixLipschitz`, `CertifiedPrefixRobust`, `TraceGrowthProfile`, `TraceBallGeometry`
-/


set_option maxHeartbeats 800000

universe u v

open List Set

variable {α : Type u} {β : Type v} {W : Type*}

/-! ## §1. Oracle Traces and Prefix Geometry -/

/-- An **oracle trace** is a finite word over an alphabet `α`.
Bridge: connects automata theory to quantum oracle semantics. -/
abbrev OracleTrace (α : Type u) := List α

/-- **Longest Common Valued Prefix Depth**: length of the longest common prefix.
Bridge: connects string combinatorics to ultrametric geometry and entropy. -/
def lcvpDepth [DecidableEq α] : OracleTrace α → OracleTrace α → ℕ
  | [], _ => 0
  | _, [] => 0
  | a :: as, b :: bs => if a = b then lcvpDepth as bs + 1 else 0

/-- **Prefix-ultrametric distance** (rational-valued).
Bridge: connects prefix geometry to non-Archimedean analysis. -/
def lcvpDist [DecidableEq α] (x y : OracleTrace α) : ℚ :=
  if x = y then 0 else 1 / (lcvpDepth x y + 1 : ℚ)

/-- **Trace ball**: all traces sharing at least `r` prefix symbols with `center`.
Bridge: connects ultrametric topology to trace-capacity counting and lattice entropy. -/
def traceBall [DecidableEq α] (center : OracleTrace α) (r : ℕ) : Set (OracleTrace α) :=
  {x | r ≤ lcvpDepth center x}

/-! ### §1.1 Depth Foundations -/

@[simp]
theorem lcvpDepth_self [DecidableEq α] (x : OracleTrace α) :
    lcvpDepth x x = x.length := by
  induction x with
  | nil => rfl
  | cons a as ih => simp [lcvpDepth, ih]








@[simp]
theorem lcvpDepth_nil_right [DecidableEq α] (x : OracleTrace α) :
    lcvpDepth x ([] : OracleTrace α) = 0 := by
  cases x <;> rfl

/-
**Ultrametric depth inequality**: the key geometric lemma.
`min (lcvpDepth x y) (lcvpDepth y z) ≤ lcvpDepth x z`

Bridge: connects prefix combinatorics to non-Archimedean geometry and
thermodynamic entropy bounds for oracle systems.
-/

/-! ### §1.2 Trace Ball Geometry -/







/-! ## §2. Weighted Transducers and Admissible Simulations -/

/-- **WeightedTraceTransducer**: A lightweight transducer model with semiring weights.
Bridge: connects rational series theory to oracle complexity and post_quantum_security. -/
structure WeightedTraceTransducer (α : Type u) (β : Type v) (W : Type*)
    [Semiring W] where
  toFun : OracleTrace α → OracleTrace β
  weight : OracleTrace α → W

/-- **AdmissibleSimulation**: bounded-distortion simulation between oracle-trace systems.
Bridge: connects coarse geometry to oracle complexity invariance and
lipschitz_certified_robustness for neural sequence classifiers. -/
structure AdmissibleSimulation (α : Type u) (β : Type v) (W : Type*)
    [DecidableEq α] [DecidableEq β] [Semiring W] where
  transducer : WeightedTraceTransducer α β W
  depth_loss : ℕ
  monotone_prefix :
    ∀ x y, lcvpDepth (transducer.toFun x) (transducer.toFun y) + depth_loss ≥ lcvpDepth x y
  weight_nontrivial : ∀ x, transducer.weight x ≠ 0

/-- **BiAdmissibleEquiv**: symmetric bi-simulation / quasi-isometry.
Bridge: connects quasi-isometry theory to machine-independent complexity. -/
structure BiAdmissibleEquiv (α : Type u) (β : Type v) (W : Type*)
    [DecidableEq α] [DecidableEq β] [Semiring W] where
  forward : AdmissibleSimulation α β W
  backward : AdmissibleSimulation β α W

/-- **PrefixLipschitz**: `(K, C)`-Lipschitz on prefix depth.
Bridge: connects to lipschitz_certified_robustness in neural sequence classification. -/
def PrefixLipschitz [DecidableEq α] [DecidableEq β]
    (f : OracleTrace α → OracleTrace β) (_K C : ℕ) : Prop :=
  ∀ x y, lcvpDepth (f x) (f y) + C ≥ lcvpDepth x y

/-- **CertifiedPrefixRobust**: certified robust with input radius `r_in`, output `r_out`.
Bridge: connects to lipschitz_certified_robustness in neural network models. -/
def CertifiedPrefixRobust [DecidableEq α] [DecidableEq β]
    (f : OracleTrace α → OracleTrace β) (r_in r_out : ℕ) : Prop :=
  ∀ x y, r_in ≤ lcvpDepth x y → r_out ≤ lcvpDepth (f x) (f y)

/-! ## §3. Simulation Calculus -/




def WeightedTraceTransducer.comp {α : Type u} {β : Type v} {γ : Type*} {W : Type*}
    [Semiring W]
    (T₁ : WeightedTraceTransducer α β W) (T₂ : WeightedTraceTransducer β γ W) :
    WeightedTraceTransducer α γ W where
  toFun := T₂.toFun ∘ T₁.toFun
  weight x := T₁.weight x * T₂.weight (T₁.toFun x)

def AdmissibleSimulation.comp {α : Type u} {β : Type v} {γ : Type*} {W : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [Semiring W] [NoZeroDivisors W]
    (S₁ : AdmissibleSimulation α β W) (S₂ : AdmissibleSimulation β γ W) :
    AdmissibleSimulation α γ W where
  transducer := S₁.transducer.comp S₂.transducer
  depth_loss := S₁.depth_loss + S₂.depth_loss
  monotone_prefix := by
    intro x y
    have h1 := S₁.monotone_prefix x y
    have h2 := S₂.monotone_prefix (S₁.transducer.toFun x) (S₁.transducer.toFun y)
    simp only [WeightedTraceTransducer.comp, Function.comp]; omega
  weight_nontrivial := by
    intro x; simp only [WeightedTraceTransducer.comp]
    exact mul_ne_zero (S₁.weight_nontrivial x) (S₂.weight_nontrivial _)





/-! ## §4. Growth, Capacity, and Trace Complexity -/


noncomputable def traceComplexity [DecidableEq α] (S : Set (OracleTrace α)) (n : ℕ) : ℕ :=
  Nat.card {x : OracleTrace α // x ∈ S ∧ x.length ≤ n}


noncomputable def capacityUpperProfile [DecidableEq α]
    (S : Set (OracleTrace α)) (n : ℕ) : ℚ :=
  (traceComplexity S n : ℚ) / (n + 1 : ℚ)

def transducedSet {α : Type u} {β : Type v} {W : Type*} [Semiring W]
    (T : WeightedTraceTransducer α β W) (S : Set (OracleTrace α)) :
    Set (OracleTrace β) :=
  T.toFun '' S




/-! ## §5. Concrete Transducers -/

def idWeightedTraceTransducer (α : Type u) (W : Type*) [Semiring W] :
    WeightedTraceTransducer α α W where
  toFun := id
  weight _ := 1

def appendSuffixTransducer {α : Type u} (s : List α) (W : Type*) [Semiring W] :
    WeightedTraceTransducer α α W where
  toFun x := x ++ s
  weight _ := 1

def dropPrefixTransducer {α : Type u} (k : ℕ) (W : Type*) [Semiring W] :
    WeightedTraceTransducer α α W where
  toFun x := x.drop k
  weight _ := 1

/-
Appending a suffix can only increase lcvpDepth (it preserves prefix agreement
and may extend it).
-/



theorem lcvpDepth_drop_le [DecidableEq α] (x y : OracleTrace α) (k : ℕ) :
    lcvpDepth x y ≤ lcvpDepth (x.drop k) (y.drop k) + k := by
  induction' k with k ih generalizing x y
  · rfl
  · cases x with
    | nil => simp [lcvpDepth, List.drop] <;> omega
    | cons a x =>
      cases y with
      | nil => simp [lcvpDepth, List.drop] <;> omega
      | cons b y =>
        by_cases h : a = b
        · have h2 := ih x y
          simp [lcvpDepth, List.drop, h] <;> omega
        · simp [lcvpDepth, List.drop, h] <;> omega


def dropPrefix_admissible [DecidableEq α] [Semiring W] [Nontrivial W]
    (k : ℕ) : AdmissibleSimulation α α W where
  transducer := dropPrefixTransducer k W
  depth_loss := k
  monotone_prefix := fun x y => lcvpDepth_drop_le x y k
  weight_nontrivial := fun _ => one_ne_zero


/-! ## §6. Main Invariance Theorems -/








/-! ## §7. Concrete Invariance and Identity -/


def id_admissible [DecidableEq α] [Semiring W] [Nontrivial W] :
    AdmissibleSimulation α α W where
  transducer := idWeightedTraceTransducer α W
  depth_loss := 0
  monotone_prefix := fun x y => by simp only [idWeightedTraceTransducer, id, Nat.add_zero]; exact le_refl _
  weight_nontrivial := fun _ => one_ne_zero

def id_biAdmissibleEquiv [DecidableEq α] [Semiring W] [Nontrivial W] :
    BiAdmissibleEquiv α α W where
  forward := id_admissible
  backward := id_admissible










/-
**take-prefix agreement from depth**.
-/


