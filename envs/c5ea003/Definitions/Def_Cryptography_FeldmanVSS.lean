-- Prove2me | Definitions.Def_Cryptography_FeldmanVSS
-- name    : Cryptography_FeldmanVSS
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:13:59.553639+00:00
-- url     : https://prove2.me/theorems/88f2b76d-1ba7-423e-9a8f-0a7557c53582
-- title:
--   Aether Catalog definitions — Cryptography_FeldmanVSS
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.FeldmanVSS`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/FeldmanVSS.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_ShamirSecretSharing

/-!
# Feldman verifiable secret sharing

We isolate the algebraic commitment interface used by Feldman's VSS.  The
codomain group is written additively: `commit a` represents the conventional
multiplicative commitment `g^a`, so addition represents multiplication of
commitments.  Injectivity says that the chosen generator has full exponent
order.  Coefficient commitments are checked by evaluating the committed
coefficient polynomial at a participant's location.
-/

namespace FeldmanVSS

open Polynomial

variable {F G : Type*} [Field F] [AddCommGroup G]


/-- Feldman's verification equation against the public coefficient commitments. -/
def verifies (commit : F →+ G) (p : F[X]) (x claimed : F) : Prop :=
  commit claimed = p.support.sum fun i => commit (p.coeff i * x ^ i)





end FeldmanVSS


