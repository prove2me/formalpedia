-- Prove2me | Theorems.Thm_Computation_DegreeMonoid_mem_iff_residue_le
-- name    : Computation.DegreeMonoid.mem_iff_residue_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:42:27.349273+00:00
-- url     : https://prove2.me/theorems/644adee9-ee55-4325-99d1-23b47a400ed9
-- title:
--   Residue criterion.
-- statement:
--   **Residue criterion.**  If `b < p` is the residue of `n` (i.e. `b*q ≡ n (mod p)`), then
--   `n` lies in `⟨p,q⟩` exactly when `b*q ≤ n`.
--
--   ```lean
--   theorem Computation.DegreeMonoid.mem_iff_residue_le(cop : Nat.Coprime p q) {n b : ℕ} (hb : b < p)
--       (hdvd : (p : ℤ) ∣ (n : ℤ) - (b : ℤ) * (q : ℤ)) :
--       n ∈ AddSubmonoid.closure ({p, q} : Set ℕ) ↔ b * q ≤ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/DegreeMonoidSylvester.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/DegreeMonoidSylvester.lean#L58

-- Thm stub generated from Speculative/AutoResearch/DegreeMonoidSylvester.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidRealisation
import Definitions.Def_Speculative_AutoResearch_DegreeMonoidStructure
/-
# Sylvester's gap count for two-loop machines

`Computation.DegreeMonoidStructure` shows that the two-loop chain machine of coprime
`p, q > 1` has a largest unrealisable computation length `p*q - p - q` (the Frobenius
number).  This file computes the *whole* obstruction, not just its maximum: the number of
computation lengths that the machine cannot realise is exactly `(p-1)*(q-1)/2`
(`sylvester_gap_ncard`), Sylvester's classical count, here proved from scratch through:

* `mem_pair_closure_iff` — membership in `⟨p,q⟩` as a two-variable representation problem;
* `exists_residue` / `mem_iff_residue_le` — the **residue criterion**: writing `b` for the
  unique residue in `[0,p)` with `b*q ≡ n (mod p)`, one has `n ∈ ⟨p,q⟩ ↔ b*q ≤ n`;
* `frobenius_symmetry` — the **symmetry of the numerical semigroup**: for `0 ≤ n ≤ F` exactly
  one of `n` and `F - n` is realisable (this is the statement that `⟨p,q⟩` is a symmetric
  numerical semigroup);
* the resulting involution `n ↦ F - n` pairs gaps with non-gaps below `F`, giving the count.

All results are proved with no `sorry`.
-/

open Computation
open DegreeMonoid


variable {p q : ℕ}

theorem Computation.DegreeMonoid.mem_iff_residue_le(cop : Nat.Coprime p q) {n b : ℕ} (hb : b < p)
    (hdvd : (p : ℤ) ∣ (n : ℤ) - (b : ℤ) * (q : ℤ)) :
    n ∈ AddSubmonoid.closure ({p, q} : Set ℕ) ↔ b * q ≤ n := by sorry
