-- Prove2me | Definitions.Def_Bridges_NeuralCoding_KWLSeparation
-- name    : Bridges_NeuralCoding_KWLSeparation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:30:15.783185+00:00
-- url     : https://prove2.me/theorems/a97ce9d6-f3b6-4330-8108-628c3cdfd6f3
-- title:
--   Aether Catalog definitions — Bridges_NeuralCoding_KWLSeparation
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.NeuralCoding.KWLSeparation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/NeuralCoding/KWLSeparation.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# k-WL Separation via Tropical Morse Spectra

This file proves that tropical Morse spectra escape the Weisfeiler–Leman
hierarchy. For every k ∈ ℕ, there exist weighted graph pairs that agree
on degree statistics but are separated by TMS cycle-death event counts.

## Main Results

* `TMS.cycle_counts_differ` — Parametric β₁ separation for all n ≥ 1
* `TMS.tms_separation_family` — Explicit TMS separation at scales n=3,4,5
* `TMS.same_edges_diff_merge_diff_cycle` — Core separation mechanism
* `TMS.wl1_blind_to_betti1` — WL1 cannot detect β₁
-/


namespace TMS

/-! ## Definitions (inlined from TropicalMorse catalog) -/

/-- Critical event types in the tropical Morse weight filtration. -/
inductive CritEvt where
  | birth | merge | cycleDeath
  deriving DecidableEq, Inhabited

/-- A Morse event: critical value + type. -/
structure MorseEvent where
  value : ℚ
  eventType : CritEvt
  deriving DecidableEq

/-- Tropical Morse spectrum: sorted list of events. -/
structure TMSpectrum where
  events : List MorseEvent
  sorted : events.Pairwise (fun a b => a.value ≤ b.value)
  deriving DecidableEq

def TMSpectrum.countType (tms : TMSpectrum) (et : CritEvt) : ℕ :=
  tms.events.countP (fun e => e.eventType == et)

def TMSpectrum.mergeCount (tms : TMSpectrum) : ℕ := tms.countType .merge
def TMSpectrum.cycleCount (tms : TMSpectrum) : ℕ := tms.countType .cycleDeath

/-- A filtration step. -/
structure FiltStep where
  edgeWeight : ℚ
  sameComponent : Bool

/-- A filtration is a sequence of edge additions. -/
structure Filtration where
  numVertices : ℕ
  steps : List FiltStep

def Filtration.mergeCount (F : Filtration) : ℕ :=
  F.steps.countP (fun s => !s.sameComponent)

def Filtration.cycleCount (F : Filtration) : ℕ :=
  F.steps.countP (fun s => s.sameComponent)


/-! ## Part 1: k-WL Equivalence Framework -/

/-- An edge-weighted graph on n vertices. -/
structure EWGraph (n : ℕ) where
  adj : Fin n → Fin n → Bool
  adj_symm : ∀ i j, adj i j = adj j i
  adj_irrefl : ∀ i, adj i i = false
  weight : Fin n → Fin n → ℚ
  weight_symm : ∀ i j, weight i j = weight j i




/-- The atomic type of a k-tuple: equality and adjacency patterns. -/
def kTupleAtomicType {n : ℕ} (G : EWGraph n) {k : ℕ}
    (t : Fin k → Fin n) : (Fin k → Fin k → Bool) × (Fin k → Fin k → Bool) :=
  (fun i j => decide (t i = t j), fun i j => G.adj (t i) (t j))

/-- k-WL equivalence via atomic type multiset agreement. -/
def WLKEquiv (k : ℕ) {n : ℕ} (G H : EWGraph n) : Prop :=
  ∀ tp : (Fin k → Fin k → Bool) × (Fin k → Fin k → Bool),
    (Finset.univ.filter (fun t : Fin k → Fin n => kTupleAtomicType G t = tp)).card =
    (Finset.univ.filter (fun t : Fin k → Fin n => kTupleAtomicType H t = tp)).card



/-! ## Part 2: Filtration Structural Theorems -/




/-! ## Part 3: List Counting Lemmas -/



/-! ## Part 4: Parametric Filtrations -/

/-- Filtration of a single cycle C_{2n}: (2n-1) merges + 1 cycle. -/
def singleCycleFilt (n : ℕ) : Filtration where
  numVertices := 2 * n
  steps := List.replicate (2 * n - 1) ⟨1, false⟩ ++ [⟨1, true⟩]

/-- Filtration of two disjoint n-cycles: 2(n-1) merges + 2 cycles. -/
def twoCycleFilt (n : ℕ) : Filtration where
  numVertices := 2 * n
  steps := List.replicate (2 * n - 2) ⟨1, false⟩ ++ [⟨1, true⟩, ⟨1, true⟩]









/-! ## Part 5: Explicit TMS Instances -/

def tmsC6 : TMSpectrum where
  events := [⟨1, .merge⟩, ⟨2, .merge⟩, ⟨3, .merge⟩, ⟨4, .merge⟩,
             ⟨5, .merge⟩, ⟨6, .cycleDeath⟩]
  sorted := by decide

def tms2C3 : TMSpectrum where
  events := [⟨1, .merge⟩, ⟨2, .merge⟩, ⟨3, .merge⟩, ⟨4, .merge⟩,
             ⟨5, .cycleDeath⟩, ⟨6, .cycleDeath⟩]
  sorted := by decide

def tmsC8 : TMSpectrum where
  events := [⟨1, .merge⟩, ⟨2, .merge⟩, ⟨3, .merge⟩, ⟨4, .merge⟩,
             ⟨5, .merge⟩, ⟨6, .merge⟩, ⟨7, .merge⟩, ⟨8, .cycleDeath⟩]
  sorted := by decide

def tms2C4 : TMSpectrum where
  events := [⟨1, .merge⟩, ⟨1, .merge⟩, ⟨2, .merge⟩, ⟨2, .merge⟩,
             ⟨3, .merge⟩, ⟨3, .merge⟩, ⟨4, .cycleDeath⟩, ⟨4, .cycleDeath⟩]
  sorted := by decide

def tmsC10 : TMSpectrum where
  events := [⟨1, .merge⟩, ⟨2, .merge⟩, ⟨3, .merge⟩, ⟨4, .merge⟩, ⟨5, .merge⟩,
             ⟨6, .merge⟩, ⟨7, .merge⟩, ⟨8, .merge⟩, ⟨9, .merge⟩, ⟨10, .cycleDeath⟩]
  sorted := by decide

def tms2C5 : TMSpectrum where
  events := [⟨1, .merge⟩, ⟨1, .merge⟩, ⟨2, .merge⟩, ⟨2, .merge⟩, ⟨3, .merge⟩,
             ⟨3, .merge⟩, ⟨4, .merge⟩, ⟨4, .merge⟩, ⟨5, .cycleDeath⟩, ⟨5, .cycleDeath⟩]
  sorted := by decide




/-! ## Part 6: Non-Uniform Weight Profile -/

/-- A non-uniform weight profile: distinct positive rational weights. -/
structure NonUniformWeight (m : ℕ) where
  w : Fin m → ℚ
  pos : ∀ i, 0 < w i
  inj : Function.Injective w


/-! ## Part 7: Main Separation Theorems -/

/-- H₁ barcode separation. -/
def H1Separates (n : ℕ) : Prop :=
  (singleCycleFilt n).cycleCount ≠ (twoCycleFilt n).cycleCount





end TMS


