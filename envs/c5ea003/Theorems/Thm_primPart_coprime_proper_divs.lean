-- Prove2me | Theorems.Thm_primPart_coprime_proper_divs
-- name    : primPart_coprime_proper_divs
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:59.320987+00:00
-- url     : https://prove2.me/theorems/94093550-1f3d-4406-be4c-b6174f8b79ac
-- title:
--   Prim part coprime proper divs
-- statement:
--   Formal statement of `primPart_coprime_proper_divs` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem primPart_coprime_proper_divs(n : ℕ) (hpp : 1 < primPart n) (d : ℕ)
--       (hd : d ∈ propDivs n) : ¬((primPart n).minFac ∣ Nat.fib d) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CarmichaelProof.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CarmichaelProof.lean#L73

-- Thm stub generated from Shared/NumberTheory/CarmichaelProof.lean
import Mathlib
import Definitions.Def_Shared_NumberTheory_CarmichaelProof
-- [catalogfix] missing module: import Shared.NumberTheory.CarmichaelHelper

/-! # Certified finite range of Carmichael's theorem (composite case)

We prove that every composite `n` with `13 ≤ n ≤ 10000` gives `F(n)` a
primitive prime divisor.
-/

set_option maxHeartbeats 800000

/-! ## Bridge Lemma -/


/-! ## Computational verification infrastructure -/




/-! ## Correctness lemmas -/

theorem primPart_coprime_proper_divs(n : ℕ) (hpp : 1 < primPart n) (d : ℕ)
    (hd : d ∈ propDivs n) : ¬((primPart n).minFac ∣ Nat.fib d) := by sorry
