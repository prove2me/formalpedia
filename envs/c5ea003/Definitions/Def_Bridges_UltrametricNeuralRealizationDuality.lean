-- Prove2me | Definitions.Def_Bridges_UltrametricNeuralRealizationDuality
-- name    : Bridges_UltrametricNeuralRealizationDuality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:45:25.898641+00:00
-- url     : https://prove2.me/theorems/df985498-1ce1-4502-b43b-7a2404f4a18e
-- title:
--   Aether Catalog definitions — Bridges_UltrametricNeuralRealizationDuality
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.UltrametricNeuralRealizationDuality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/UltrametricNeuralRealizationDuality.lean by skeleton subtraction
import Mathlib
/-
# Ultrametric Neural Realization Duality

A **Myhill–Nerode theory for ultrametric neural systems**: finite realization,
minimality, and uniqueness theorems for observer-response systems with
ultrametric state dynamics.

## Main Results

- **Observer indistinguishability** is an equivalence relation (§2)
- **Step and output maps** respect observer indistinguishability (§3)
- **Nonexpansion composition**: ultrametric contraction composes cleanly (§5)
- **Morphism injectivity**: morphisms from minimal realizations are injective (§6)
- **Morphism surjectivity**: morphisms to minimal targets are surjective (§12)
- **Uniqueness**: minimal realizations are unique up to bijection (§12)
- **Finite realization**: finite-rank kernels yield finite predictors (§14)
- **Bridge theorem**: combines all into the ultrametric Nerode theory (§15)
-/


set_option maxHeartbeats 800000

open Function

noncomputable section

/-! ## §1. Core Definitions -/

/-- Iterated transition: apply a word to a state. -/
def applyWord {X Q : Type*} (step : X → Q → Q) : List X → Q → Q
  | [], q => q
  | x :: xs, q => applyWord step xs (step x q)




/-- The response kernel: observer output after processing a word. -/
def responseKernel {S X O Q : Type*}
    (step : X → Q → Q) (output : O → Q → S)
    (w : List X) (o : O) (q : Q) : S :=
  output o (applyWord step w q)

/-! ## §2. Observer Indistinguishability -/

/-- Two states are **observer-indistinguishable** if they produce identical
    responses for all input words and all observers. -/
def ObsIndist {S X O Q : Type*}
    (step : X → Q → Q) (output : O → Q → S) (q₁ q₂ : Q) : Prop :=
  ∀ (w : List X) (o : O),
    responseKernel step output w o q₁ = responseKernel step output w o q₂





/-! ## §3. Step and Output Preserve Indistinguishability -/




/-! ## §4. Ultrametric Predictor Signatures -/

/-- An ultrametric predictor signature. -/
structure UltraSig (S X O Q : Type*) where
  step : X → Q → Q
  output : O → Q → S
  init : Q
  udist : Q → Q → ℝ
  udist_nonneg : ∀ a b, 0 ≤ udist a b
  udist_self : ∀ a, udist a a = 0
  udist_symm : ∀ a b, udist a b = udist b a
  udist_ultra : ∀ a b c, udist a c ≤ max (udist a b) (udist b c)
  nonexpanding : ∀ x q₁ q₂, udist (step x q₁) (step x q₂) ≤ udist q₁ q₂

def UltraSig.kernel {S X O Q : Type*}
    (sig : UltraSig S X O Q) (w : List X) (o : O) : S :=
  responseKernel sig.step sig.output w o sig.init

def Realizes {S X O Q : Type*}
    (sig : UltraSig S X O Q) (K : List X → O → S) : Prop :=
  ∀ (w : List X) (o : O), sig.kernel w o = K w o

def SameKernel {S X O Q₁ Q₂ : Type*}
    (sig₁ : UltraSig S X O Q₁) (sig₂ : UltraSig S X O Q₂) : Prop :=
  ∀ (w : List X) (o : O), sig₁.kernel w o = sig₂.kernel w o

def UReachable {S X O Q : Type*} (sig : UltraSig S X O Q) (q : Q) : Prop :=
  ∃ w : List X, applyWord sig.step w sig.init = q

def AllReach {S X O Q : Type*} (sig : UltraSig S X O Q) : Prop :=
  ∀ q : Q, UReachable sig q

def AllObs {S X O Q : Type*} (sig : UltraSig S X O Q) : Prop :=
  ∀ q₁ q₂ : Q, ObsIndist sig.step sig.output q₁ q₂ → q₁ = q₂

/-- **Minimal realization: reachable and observable.** -/
def IsMinimal {S X O Q : Type*} (sig : UltraSig S X O Q) : Prop :=
  AllReach sig ∧ AllObs sig



/-! ## §5. Nonexpansion Under Word Application -/


/-! ## §6. Signature Morphisms -/

/-- A morphism between predictor signatures. -/
structure SigMorphism {S X O Q₁ Q₂ : Type*}
    (sig₁ : UltraSig S X O Q₁) (sig₂ : UltraSig S X O Q₂) where
  toFun : Q₁ → Q₂
  map_init : toFun sig₁.init = sig₂.init
  map_step : ∀ x q, toFun (sig₁.step x q) = sig₂.step x (toFun q)
  map_output : ∀ o q, sig₁.output o q = sig₂.output o (toFun q)







/-! ## §7. Nerode Equivalence -/

/-- Two words are **Nerode-equivalent** relative to a kernel. -/
def NerodeEq {S X O : Type*} (K : List X → O → S) (w₁ w₂ : List X) : Prop :=
  ∀ (v : List X) (o : O), K (w₁ ++ v) o = K (w₂ ++ v) o




/-! ## §8. Realization ↔ Nerode Correspondence -/


/-! ## §9. Isometric Equivalences -/

/-- An isometric equivalence between predictor signatures. -/
structure IsoSigEquiv {S X O Q₁ Q₂ : Type*}
    (sig₁ : UltraSig S X O Q₁) (sig₂ : UltraSig S X O Q₂) where
  equiv : Q₁ ≃ Q₂
  map_init : equiv sig₁.init = sig₂.init
  map_step : ∀ x q, equiv (sig₁.step x q) = sig₂.step x (equiv q)
  map_output : ∀ o q, sig₁.output o q = sig₂.output o (equiv q)
  isometry : ∀ q₁ q₂, sig₂.udist (equiv q₁) (equiv q₂) = sig₁.udist q₁ q₂

/-- An isometric equivalence induces a morphism. -/
def IsoSigEquiv.toMorphism {S X O Q₁ Q₂ : Type*}
    {sig₁ : UltraSig S X O Q₁} {sig₂ : UltraSig S X O Q₂}
    (e : IsoSigEquiv sig₁ sig₂) : SigMorphism sig₁ sig₂ :=
  { toFun := e.equiv, map_init := e.map_init,
    map_step := e.map_step, map_output := e.map_output }


/-! ## §10. Discrete Ultrametric -/

/-- The discrete ultrametric: d(x,y) = 0 if x = y, 1 otherwise. -/
def discreteUDist {Q : Type*} [DecidableEq Q] (q₁ q₂ : Q) : ℝ :=
  if q₁ = q₂ then 0 else 1

theorem discreteUDist_nonneg {Q : Type*} [DecidableEq Q] (a b : Q) :
    0 ≤ discreteUDist a b := by unfold discreteUDist; split <;> norm_num

theorem discreteUDist_self {Q : Type*} [DecidableEq Q] (a : Q) :
    discreteUDist a a = 0 := if_pos rfl

theorem discreteUDist_symm {Q : Type*} [DecidableEq Q] (a b : Q) :
    discreteUDist a b = discreteUDist b a := by
  unfold discreteUDist; by_cases h : a = b <;> simp [h, eq_comm]

theorem discreteUDist_ultra {Q : Type*} [DecidableEq Q] (a b c : Q) :
    discreteUDist a c ≤ max (discreteUDist a b) (discreteUDist b c) := by
  simp only [discreteUDist]
  split <;> rename_i hac
  · split <;> split <;> simp_all
  · by_cases hab : a = b
    · subst hab; split <;> simp_all
    · simp only [hab, ite_false]; exact le_max_left _ _

theorem discreteUDist_nonexpanding {Q : Type*} [DecidableEq Q]
    (f : Q → Q) (q₁ q₂ : Q) :
    discreteUDist (f q₁) (f q₂) ≤ discreteUDist q₁ q₂ := by
  unfold discreteUDist
  by_cases h : q₁ = q₂
  · simp [h]
  · by_cases hf : f q₁ = f q₂ <;> simp [h, hf]

/-- Build a predictor with discrete ultrametric. -/
def mkDiscreteSig {S X O Q : Type*} [DecidableEq Q]
    (step : X → Q → Q) (output : O → Q → S) (init : Q) :
    UltraSig S X O Q :=
  { step, output, init
    udist := discreteUDist
    udist_nonneg := discreteUDist_nonneg
    udist_self := discreteUDist_self
    udist_symm := discreteUDist_symm
    udist_ultra := discreteUDist_ultra
    nonexpanding := fun x => discreteUDist_nonexpanding (step x) }

/-! ## §11. Concrete Example: Parity Automaton -/

/-- A two-state parity automaton. -/
def parityAut : UltraSig ℕ Bool Unit (Fin 2) :=
  mkDiscreteSig
    (fun b q => if b then (q + 1) % 2 else q)
    (fun () q => q.val) 0




/-! ## §12. Uniqueness of Minimal Realizations -/





/-! ## §13. Residual Tracking Lemma -/


/-! ## §14. Finite Realization Theorem -/


/-! ## §15. Ultrametric Nerode Bridge Theorem -/


/-! ## §16. Universal Property -/


end


