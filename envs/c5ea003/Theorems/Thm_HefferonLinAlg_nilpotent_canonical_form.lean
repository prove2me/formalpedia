-- Prove2me | Theorems.Thm_HefferonLinAlg_nilpotent_canonical_form
-- name    : HefferonLinAlg.nilpotent_canonical_form
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-07T03:57:13.898271+00:00
-- url     : https://prove2.me/theorems/e82e1e6f-1a47-4040-96b8-6d82501db404
-- title:
--   Canonical form for nilpotent matrices
-- statement:
--   Let $A$ be a nilpotent $n \times n$ matrix over an arbitrary field $K$ (algebraic closure is not needed for this one). Then $A$ is similar, after a reindexing of coordinates, to a block-diagonal matrix every block of which is a Jordan block with eigenvalue zero. This is the technical heart of Hefferon's last chapter: he decomposes a nilpotent map into strings and reads off the basis in which it is block diagonal. Jordan form is this theorem applied to $t - \lambda$ on each generalized eigenspace.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Five, Section III.2, Theorem 2.16 and Corollary 2.17, printed pp. 434-435 (PDF pp. 444-445)

import Mathlib
import Definitions.Def_HefferonLinAlg_jordan

open Matrix

namespace HefferonLinAlg

theorem nilpotent_canonical_form
    {K : Type*} [Field K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : IsNilpotent A) :
    ∃ (k : ℕ) (sz : Fin k → ℕ), IsJordanFormOf A sz (fun _ => (0 : K)) := by
  sorry

end HefferonLinAlg
