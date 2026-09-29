-- Prove2me | Theorems.Thm_StoneDualityNeuralNetworks_duplicate_neurons_range
-- name    : StoneDualityNeuralNetworks.duplicate_neurons_range
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T12:23:23.222717+00:00
-- url     : https://prove2.me/theorems/3d9d394d-8aca-4ac0-b61e-fce5bf82cbca
-- title:
--   Two neurons having the same threshold can realize only the two constant activation
-- statement:
--   Two neurons having the same threshold can realize only the two constant activation
--   patterns, not all four elements of `Fin 2 → Bool`.
--
--   ```lean
--   theorem StoneDualityNeuralNetworks.duplicate_neurons_range:
--       Set.range (activationVector (k := 2) (fun _ => 0)) =
--         {p | p = (fun _ => false) ∨ p = (fun _ => true)} := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/StoneDualityNeuralNetworks.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/StoneDualityNeuralNetworks.lean#L44

-- Thm stub generated from Logic/StoneDualityNeuralNetworks.lean
import Mathlib
import Definitions.Def_Logic_StoneDualityNeuralNetworks

/-!
# Stone duality and neural classifiers: precise positive results and counterexamples

A classifier induces a Boolean algebra of observable predicates, but several stronger
claims in the proposed framing fail.  This file isolates the failures without assuming
any particular implementation of neural networks.
-/

open StoneDualityNeuralNetworks

theorem StoneDualityNeuralNetworks.duplicate_neurons_range:
    Set.range (activationVector (k := 2) (fun _ => 0)) =
      {p | p = (fun _ => false) ∨ p = (fun _ => true)} := by sorry
