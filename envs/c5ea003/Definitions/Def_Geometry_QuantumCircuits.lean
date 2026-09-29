-- Prove2me | Definitions.Def_Geometry_QuantumCircuits
-- name    : Geometry_QuantumCircuits
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:51:51.554953+00:00
-- url     : https://prove2.me/theorems/eb8f73bd-32aa-4dbd-b1c1-b19212a8cac6
-- title:
--   Aether Catalog definitions — Geometry_QuantumCircuits
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.QuantumCircuits`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/QuantumCircuits.lean by skeleton subtraction
import Mathlib

open Matrix
/-! # CatalogBuild.Physics.Quantum.QuantumCircuits

Auto-generated from theorem catalog database.
Domain: Physics/Quantum
Declarations: 44
-/

/-- Pauli X (NOT gate): [[0,1],[1,0]] -/
def pauli_X : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- Pauli Z (phase gate): [[1,0],[0,-1]] -/
def pauli_Z : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, -1]

/-- Pauli XZ: [[0,-1],[1,0]] (= iY up to scalar) -/
def pauli_XZ : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]









/-- Scaled Hadamard: 2H = [[1,1],[1,-1]] (avoids √2). -/
def hadamard_scaled : Matrix (Fin 2) (Fin 2) ℤ := !![1, 1; 1, -1]





/-- The CNOT gate as a 4×4 integer matrix. -/
def CNOT : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 1;
     0, 0, 1, 0]



/-- The Toffoli gate as an 8×8 integer matrix. -/
def Toffoli : Matrix (Fin 8) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 0, 0, 1, 0]



/-- The SWAP gate exchanges two qubits. -/
def SWAP_gate : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 0, 1, 0;
     0, 1, 0, 0;
     0, 0, 0, 1]



/-- The CZ (controlled-Z) gate. -/
def CZ_gate : Matrix (Fin 4) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, -1]






/-- The [7,4,3] Hamming code parity check matrix (classical backbone of Steane code). -/
def hamming_parity : Matrix (Fin 3) (Fin 7) (ZMod 2) :=
  !![1, 0, 0, 1, 1, 0, 1;
     0, 1, 0, 1, 0, 1, 1;
     0, 0, 1, 0, 1, 1, 1]



/-- A quantum circuit over a gate set G is a list of (gate, qubit_indices) pairs. -/
structure QuantumCircuit (G : Type*) (n : ℕ) where
  gates : List (G × Fin n)

/-- Circuit depth = number of gates. -/
def QuantumCircuit.depth {G : Type*} {n : ℕ} (c : QuantumCircuit G n) : ℕ :=
  c.gates.length

/-- Sequential composition of circuits. -/
def QuantumCircuit.seq {G : Type*} {n : ℕ}
    (c₁ c₂ : QuantumCircuit G n) : QuantumCircuit G n where
  gates := c₁.gates ++ c₂.gates


/-- The identity circuit has depth 0. -/
def QuantumCircuit.identity (G : Type*) (n : ℕ) : QuantumCircuit G n where
  gates := []


