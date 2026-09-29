-- Prove2me | Definitions.Def_Applications_BSD_RankComputability
-- name    : Applications_BSD_RankComputability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:32:03.167536+00:00
-- url     : https://prove2.me/theorems/f4a01587-93f4-4234-ab83-f163f710323f
-- title:
--   Aether Catalog definitions — Applications_BSD_RankComputability
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.BSD.RankComputability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/BSD/RankComputability.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic.
Released under Apache 2.0 license.

# Certified rank computation from a finite descent presentation

The unconditional computability of Mordell–Weil ranks over `ℚ` is not presently
known.  This file isolates and proves the finite linear-algebra endpoint used by
descent: once a descent supplies a rational presentation matrix for the free
part, its rank is computed by Gaussian elimination (`Matrix.rank`).
-/

namespace BSD.RankComputability

/-- The candidate free rank associated with a presentation having `n` generators
and relation matrix `A`. -/
noncomputable def descentRank {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) : ℕ :=
  n - A.rank








end BSD.RankComputability


