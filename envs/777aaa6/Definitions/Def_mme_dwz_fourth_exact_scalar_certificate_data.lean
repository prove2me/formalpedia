-- Prove2me | Definitions.Def_mme_dwz_fourth_exact_scalar_certificate_data
-- name    : mme_dwz_fourth_exact_scalar_certificate_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T08:22:42.608161+00:00
-- url     : https://prove2.me/theorems/9f88f986-96f9-4415-926a-dcc910f497d4
-- title:
--   Soundness of every retained-floor obligation of the scalar ledger
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_exact_scalar_certificate, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_exact_retained_entropy_arithmetic_data
import Theorems.Thm_mme_dwz_fourth_exact_retained_entropy_arithmetic
import Theorems.Thm_mme_dwz_fourth_log_lookup_sound

open MME
open MME.DWZFourthLogScaleTable
open MME.DWZFourthRetainedEntropy
open scoped Classical

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthExactScalarCertificate

/-- `entropyActual` with the table lookup as a parameter.  Its equation lemmas are generic;
stated directly over `entries[i]?`, generating them makes Lean reduce the concrete table. -/
noncomputable def entropyActualWith (tbl : Nat → Option (Rat × Nat)) : List Nat → ℝ
  | [] => 0
  | logIndex :: tail =>
      match tbl logIndex with
      | none => entropyActualWith tbl tail
      | some entry => Real.negMulLog (entry.1 : ℝ) + entropyActualWith tbl tail

noncomputable def entropyActual (cells : List Nat) : ℝ :=
  entropyActualWith (fun i ↦ entries[i]?) cells

noncomputable def termActual (term : EntropyTerm) : Option ℝ := do
  let record ← entropyRecords[term.recordIndex]?
  pure ((term.coefficient : ℝ) * entropyActual record.cells)

noncomputable def termsActual : List EntropyTerm → Option ℝ
  | [] => some 0
  | term :: tail => do
      let value ← termActual term
      let rest ← termsActual tail
      pure (value + rest)

end MME.DWZFourthExactScalarCertificate


